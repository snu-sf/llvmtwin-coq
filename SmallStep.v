Require Import Common.
Require Import Memory.
Require Import Value.
Require Import Lang.
Require Import State.
Require Import BinNatDef.
Require Import LoadStore.
Require Import List.
Require Import Bool.


Module Ir.

Module SmallStep.

Import Ir.Inst.


Definition twos_compl (n:N) (sz:nat):N :=
  N.modulo n (N.shiftl 2%N (N.of_nat sz)).

Definition twos_compl2 (n:nat) (sz:nat):N :=
  N.modulo (N.of_nat n) (N.shiftl 2%N (N.of_nat sz)).

Definition twos_compl_add (x y:N) (sz:nat):N :=
  twos_compl (N.add x y) sz.

Definition twos_compl_sub (x y:N) (sz:nat):N :=
  twos_compl (N.sub (N.add x (N.shiftl 2%N (N.of_nat sz))) y) sz.


Definition p2N (p:Ir.ptrval) (m:Ir.Memory.t) (sz:nat):N :=
  match p with
  | Ir.plog (l, o) =>
    match Ir.log_to_phy m l o with
    | Some (Ir.pphy (o', _, _)) =>
      twos_compl2 o' sz
    | _ => 0%N
    end
  | Ir.pphy (o, _, _) =>
    twos_compl2 o sz
  end.

Definition psub p1 p2 m bsz :=
  let s := N.shiftl 2%N (N.of_nat bsz) in
  match (p1, p2) with
  | (Ir.plog (l1, o1), Ir.plog (l2, o2)) =>
    if Nat.eqb l1 l2 then
      Ir.num (twos_compl_sub (N.of_nat o1) (N.of_nat o2) bsz)
    else Ir.poison
  | (Ir.pphy (o1, _, _), Ir.plog _) =>
    Ir.num (twos_compl_sub (N.of_nat o1) (p2N p2 m bsz) bsz)
  | (Ir.plog _, Ir.pphy (o2, _, _)) =>
    Ir.num (twos_compl_sub (p2N p1 m bsz) (N.of_nat o2) bsz)
  | (Ir.pphy (o1, _, _), Ir.pphy (o2, _, _)) =>
    Ir.num (twos_compl_sub (N.of_nat o1) (N.of_nat o2) bsz)
  end.

Definition gep (p:Ir.ptrval) (idx:N) (t:Ir.ty) (m:Ir.Memory.t): Ir.val :=
  match p with
  | Ir.plog (l, o) =>
    match (Ir.Memory.get m l) with
    | Some blk =>
      let o' := (N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ)) in
      if Ir.MemBlock.inbounds o blk &&
         Ir.MemBlock.inbounds o' blk then Ir.ptr (Ir.plog (l, o'))
      else Ir.poison (* out of bounds *)
    | None => Ir.poison (* unreachable *)
    end
  | Ir.pphy (o, Is, cid) =>
    Ir.ptr (Ir.pphy (o,
                     (N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ))::Is, cid))
  end.

Definition free p m: option (Ir.Memory.t) :=
  match p with
  | Ir.plog (l, 0) => Ir.Memory.free m l
  | Ir.pphy (o, Is, cid) =>
    match (Ir.Memory.zeroofs_block m o) with
    | None => None
    | Some (bid, mb) =>
      if Ir.deref m p 1 then (* to use Is, cid info *)
        Ir.Memory.free m bid
      else None
    end
  | _ => None
  end.

Definition to_num (b:bool): Ir.val :=
  Ir.num (if b then 1%N else 0%N).

(* Semantics of instructions which behave deterministically. *)
Definition step_det (c:Ir.Config.t) (i:Ir.Inst.t)
: option (Ir.event * Ir.Config.t) :=
  match i with
  | iadd r (Ir.ity bsz) op1 op2 =>
    Some (Ir.e_none,
      Ir.Config.update_rval c r
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      | (Some (Ir.num i1), Some (Ir.num i2)) =>
        Ir.num (twos_compl_add i1 i2 bsz)
      | (_, _) => Ir.poison
      end)

  | isub r (Ir.ity bsz) op1 op2 =>
    Some (Ir.e_none,
      Ir.Config.update_rval c r
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      | (Some (Ir.num i1), Some (Ir.num i2)) =>
        Ir.num (twos_compl_sub i1 i2 bsz)
      | (_, _) => Ir.poison
      end)

  | ipsub r (Ir.ity bsz) (Ir.ptrty opty) op1 op2 =>
    Some (Ir.e_none,
      Ir.Config.update_rval c r
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
        psub p1 p2 (Ir.Config.m c) bsz
      | (_, _) => Ir.poison
      end)

  | igep r (Ir.ptrty retty) opptr opidx inb =>
    Some (Ir.e_none,
      Ir.Config.update_rval c r
      match (Ir.Config.get_val c opptr, Ir.Config.get_val c opidx) with
      | (Some (Ir.ptr p), Some (Ir.num idx)) =>
        gep p idx retty (Ir.Config.m c)
      | (_, _) => Ir.poison
      end)

  | iload r retty opptr =>
    match (Ir.Config.get_val c opptr) with
    | (Some (Ir.ptr p)) =>
      if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz retty) then
        Some (Ir.e_none,
              (Ir.Config.update_rval c r
              (Ir.load_val (Ir.Config.m c) p retty)))
      else None
    | _ => None
    end

  | istore valty opptr opval =>
    match (Ir.Config.get_val c opptr, Ir.Config.get_val c opval) with
    | (Some (Ir.ptr p), Some v) =>
      if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz valty) then
        Some (Ir.e_none,
              Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty))
      else None
    | (_, _) => None
    end

  | imalloc r opty opval =>
    (* malloc is not determinstic! *)
    None

  | ifree opptr =>
    match (Ir.Config.get_val c opptr) with
    | Some (Ir.ptr p) =>
      match (free p (Ir.Config.m c)) with
      | Some m => Some (Ir.e_none, Ir.Config.update_m c m)
      | None => None
      end
    | _ => None
    end

  | iptrtoint r opptr (Ir.ity retty) =>
    Some (Ir.e_none, Ir.Config.update_rval c r
      match (Ir.Config.get_val c opptr) with
      | Some (Ir.ptr p) => (Ir.num (p2N p (Ir.Config.m c) retty))
      | _ => Ir.poison
      end)

  | iinttoptr r opint (Ir.ptrty retty) =>
    Some (Ir.e_none, Ir.Config.update_rval c r
      match (Ir.Config.get_val c opint) with
      | Some (Ir.num n) =>
        Ir.ptr (Ir.pphy (N.to_nat n, nil, None))
      | _=> Ir.poison
      end)

  | ievent opval =>
    match (Ir.Config.get_val c opval) with
    | Some v => Some (Ir.e_some v, c)
    | None => None
    end

  | iicmp_eq r opty op1 op2 =>
    match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
    (* Integer comparison *)
    | (Some (Ir.num n1), Some (Ir.num n2)) =>
      Some (Ir.e_none, Ir.Config.update_rval c r (to_num (N.eqb n1 n2)))
    (* Comparison with poison *)
    | (Some (Ir.poison), _) =>
      Some (Ir.e_none, Ir.Config.update_rval c r Ir.poison)
    | (_, Some (Ir.poison)) =>
      Some (Ir.e_none, Ir.Config.update_rval c r Ir.poison)
    (* Pointer comparison *)
    | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
      let m := Ir.Config.m c in
      match (p1, p2) with
      | (Ir.plog (l1, o1), Ir.plog (l2, o2)) =>
        if Nat.eqb l1 l2 then
          (* ICMP-PTR-LOGICAL *)
          Some (Ir.e_none, Ir.Config.update_rval c r (to_num (Nat.eqb o1 o2)))
        else
          match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
          | (Some mb1, Some mb2) =>
            (* ICMP-PTR-LOGICAL' *)
            if Nat.leb o1 (Ir.MemBlock.n mb1) && Nat.leb o2 (Ir.MemBlock.n mb2) then
              Some (Ir.e_none, Ir.Config.update_rval c r (to_num false))
            else
              (* ICMP-PTR-LOGICAL-NONDET-TRUE *)
              None
          | (_, _) => None
          end
      | (Ir.pphy (o1, Is1, cid1), _) =>
        Some (Ir.e_none, Ir.Config.update_rval c r
               (to_num (N.eqb (N.of_nat o1) (p2N p2 m Ir.PTRSZ))))
      | (_, Ir.pphy (o2, Is2, cid2)) =>
        Some (Ir.e_none, Ir.Config.update_rval c r
               (to_num (N.eqb (p2N p1 m Ir.PTRSZ) (N.of_nat o2))))
      end
    | (_, _) => None (* In other cases, it is nondeterministic. *)
    end

  | iicmp_ule r opty opptr1 opttr2 =>
    match (Ir.Config.get_val c opptr1, Ir.Config.get_val c opptr2) with
    | (Some (Ir.num n1), Some (Ir.num n2)) =>
      Nat.leb n1 n2
    |

  | _ => None (* Untyped IR *)
  end.

End SmallStep.

End Ir.
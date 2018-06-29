Require Import List.
Require Import Bool.
Require Import BinNatDef.

Require Import Common.
Require Import Memory.
Require Import Value.
Require Import Lang.
Require Import State.
Require Import LoadStore.
Require Import Behaviors.


Module Ir.

Module SmallStep.

Import Ir.Inst.


(* Returns basic block id of pc *)
Definition pc_bbid (p:Ir.IRFunction.pc): nat :=
  match p with
  | Ir.IRFunction.pc_phi bbid _ => bbid
  | Ir.IRFunction.pc_inst bbid _ => bbid
  | Ir.IRFunction.pc_terminator bbid => bbid
  end.

(* Increment pc of the config. *)
Definition incrpc (c:Ir.Config.t) :=
  match (Ir.Config.cur_fdef_pc c) with
  | Some (fdef, pc0) =>
    match (Ir.IRFunction.next_trivial_pc pc0 fdef) with
    | Some pc' =>
      Ir.Config.update_pc c pc'
    | None => c (* Cannot happen..! *)
    end
  | None => c (* Cannot happen *)
  end.

Definition update_reg_and_incrpc (c:Ir.Config.t) (r:Ir.reg) (v:Ir.val) :=
  incrpc (Ir.Config.update_rval c r v).


(* Helper functions *)
Definition twos_compl (n:N) (sz:nat):N :=
  N.modulo n (N.shiftl 2%N (N.of_nat sz)).

Definition twos_compl2 (n:nat) (sz:nat):N :=
  N.modulo (N.of_nat n) (N.shiftl 2%N (N.of_nat sz)).

Definition twos_compl_add (x y:N) (sz:nat):N :=
  twos_compl (N.add x y) sz.

Definition twos_compl_sub (x y:N) (sz:nat):N :=
  twos_compl (N.sub (N.add x (N.shiftl 2%N (N.of_nat sz))) y) sz.

Definition to_num (b:bool): Ir.val :=
  Ir.num (if b then 1%N else 0%N).


(* Convert a pointer into N. *)
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

(* Pointer subtraction. *)
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

(* getelementptr with/without inbounds tag. *)
Definition gep (p:Ir.ptrval) (idx0:N) (t:Ir.ty) (m:Ir.Memory.t) (inb:bool): Ir.val :=
  let idx := N.mul idx0 (N.of_nat (Ir.ty_bytesz t)) in
  match p with
  | Ir.plog (l, o) =>
    let o' := N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ) in
    if inb then
      match (Ir.Memory.get m l) with
      | Some blk =>
        if Ir.MemBlock.inbounds o blk &&
           Ir.MemBlock.inbounds o' blk then Ir.ptr (Ir.plog (l, o'))
        else Ir.poison (* out of bounds *)
      | None => Ir.poison (* unreachable *)
      end
    else Ir.ptr (Ir.plog (l, o'))
  | Ir.pphy (o, Is, cid) =>
    let o' := N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ) in
    if inb then
      if N.ltb idx (N.shiftl 1 (N.sub (N.of_nat Ir.PTRSZ) 1%N)) then
        (* Added idx is positive. *)
        if Nat.ltb o' Ir.MEMSZ then
          (* Should not overflow Ir.MEMSZ *)
          Ir.ptr (Ir.pphy (o', o::o'::Is, cid))
        else Ir.poison
      else
        (* idx is negative: no constraint. *)
        Ir.ptr (Ir.pphy (o', o::o'::Is, cid))
    else
      Ir.ptr (Ir.pphy (o', Is, cid))
  end.

(* free operation. *)
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

(* p1 == p2 *)
Definition icmp_eq_ptr (p1 p2:Ir.ptrval) (m:Ir.Memory.t): option bool :=
  match (p1, p2) with
  | (Ir.plog (l1, o1), Ir.plog (l2, o2)) =>
    if Nat.eqb l1 l2 then
      (* ICMP-PTR-LOGICAL *)
      Some (Nat.eqb o1 o2)
    else
      match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
      | (Some mb1, Some mb2) =>
        (* ICMP-PTR-LOGICAL' *)
        if Nat.leb o1 (Ir.MemBlock.n mb1) && Nat.leb o2 (Ir.MemBlock.n mb2) then
          Some false
        else
          (* ICMP-PTR-LOGICAL-NONDET-TRUE *)
          None
      | (_, _) => None
      end
  | (Ir.pphy (o1, Is1, cid1), _) =>
    Some (N.eqb (N.of_nat o1) (p2N p2 m Ir.PTRSZ))
  | (_, Ir.pphy (o2, Is2, cid2)) =>
    Some (N.eqb (p2N p1 m Ir.PTRSZ) (N.of_nat o2))
  end.

(* p1 <= p2 *)
Definition icmp_ule_ptr (p1 p2:Ir.ptrval) (m:Ir.Memory.t): option bool :=
  match (p1, p2) with
  | (Ir.plog (l1, o1), Ir.plog (l2, o2)) =>
    if Nat.eqb l1 l2 then
      match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
      | (Some mb1, Some mb2) =>
        if Nat.leb o1 (Ir.MemBlock.n mb1) && Nat.leb o2 (Ir.MemBlock.n mb2) then
          Some (Nat.leb o1 o2)
        else None (* nondet. value *)
      | (_, _) => None
      end
    else None (* nondet. value *)
  | (Ir.pphy (o1, Is1, cid1), _) =>
    Some (N.leb (N.of_nat o1) (p2N p2 m Ir.PTRSZ))
  | (_, Ir.pphy (o2, Is2, cid2)) =>
    Some (N.leb (p2N p1 m Ir.PTRSZ) (N.of_nat o2))
  end.

Definition binop (bopc:Ir.Inst.bopcode) (i1 i2:N) (bsz:nat):N :=
  match bopc with
  | Ir.Inst.bop_add => twos_compl_add i1 i2 bsz
  | Ir.Inst.bop_sub => twos_compl_sub i1 i2 bsz
  end.

Inductive step_res :=
| sr_success: Ir.event -> Ir.Config.t -> step_res
| sr_goes_wrong: step_res (* went wrong. *)
| sr_oom: step_res (* out-of-memory *)
| sr_nondet: step_res (* has non-deterministic result. *)
| sr_prog_finish: Ir.val -> step_res (* program has finished (with following integer). *)
.

(* Semantics of an instruction which behaves deterministically.
   If running the instruction raises nondeterministic result,
   this function returns sr_goes_wrong. *)
Definition inst_det (c:Ir.Config.t) (i:Ir.Inst.t): step_res :=
  match i with
  | ibinop r (Ir.ity bsz) bopc op1 op2 =>
    match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
    | (Some (Ir.num i1), Some (Ir.num i2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num (binop bopc i1 i2 bsz)))
    | (Some Ir.poison, Some (Ir.num i2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (Some (Ir.num i2), Some Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (_, _) => sr_goes_wrong
    end

  | ipsub r (Ir.ity bsz) (Ir.ptrty opty) op1 op2 =>
    match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
    | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r (psub p1 p2 (Ir.Config.m c) bsz))
    | (Some Ir.poison, Some (Ir.ptr p2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (Some (Ir.ptr p1), Some Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (_, _) => sr_goes_wrong
    end

  | igep r (Ir.ptrty retty) opptr opidx inb =>
    match (Ir.Config.get_val c opptr, Ir.Config.get_val c opidx) with
    | (Some (Ir.ptr p), Some (Ir.num idx)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r (gep p idx retty (Ir.Config.m c) inb))
    | (Some Ir.poison, Some (Ir.num idx)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (Some (Ir.ptr p), Some Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (_, _) => sr_goes_wrong
    end

  | iload r retty opptr =>
    match (Ir.Config.get_val c opptr) with
    | (Some (Ir.ptr p)) =>
      if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz retty) then
        sr_success Ir.e_none (update_reg_and_incrpc c r
              (Ir.load_val (Ir.Config.m c) p retty))
      else sr_goes_wrong
    | _ => sr_goes_wrong
    end

  | istore valty opptr opval =>
    match (Ir.Config.get_val c opptr, Ir.Config.get_val c opval) with
    | (Some (Ir.ptr p), Some v) =>
      if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz valty) then
        sr_success Ir.e_none
              (incrpc (Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty)))
      else sr_goes_wrong
    | (_, _) => sr_goes_wrong
    end

  | imalloc r opty opval =>
    (* malloc is not determinstic! *)
    sr_nondet

  | ifree opptr =>
    match (Ir.Config.get_val c opptr) with
    | Some (Ir.ptr p) =>
      match (free p (Ir.Config.m c)) with
      | Some m => sr_success Ir.e_none (incrpc (Ir.Config.update_m c m))
      | None => sr_goes_wrong
      end
    | _ => sr_goes_wrong
    end

  | iptrtoint r opptr (Ir.ity retty) =>
    match (Ir.Config.get_val c opptr) with
    | Some (Ir.ptr p) =>
      sr_success Ir.e_none
                 (update_reg_and_incrpc c r (Ir.num (p2N p (Ir.Config.m c) retty)))
    | Some (Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | _ => sr_goes_wrong
    end

  | iinttoptr r opint (Ir.ptrty retty) =>
    match (Ir.Config.get_val c opint) with
    | Some (Ir.num n) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r
        (Ir.ptr (Ir.pphy (N.to_nat n, nil, None))))
    | Some (Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | _=> sr_goes_wrong
    end

  | ievent opval =>
    match (Ir.Config.get_val c opval) with
    | Some (Ir.num n) => sr_success (Ir.e_some n) (incrpc c)
    | _ => sr_goes_wrong
    end

  | iicmp_eq r opty op1 op2 =>
    match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
    (* Integer comparison *)
    | (Some (Ir.num n1), Some (Ir.num n2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (N.eqb n1 n2)))
    (* Comparison with poison *)
    | (Some (Ir.poison), _) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (_, Some (Ir.poison)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    (* Pointer comparison *)
    | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
      match (icmp_eq_ptr p1 p2 (Ir.Config.m c)) with
      | Some b =>  sr_success Ir.e_none (update_reg_and_incrpc c r (to_num b))
      | None => sr_goes_wrong
      end
    | (_, _) => sr_goes_wrong (* In other cases, it is untyped. *)
    end

  | iicmp_ule r opty opptr1 opptr2 =>
    match (Ir.Config.get_val c opptr1, Ir.Config.get_val c opptr2) with
    (* Integer comparison *)
    | (Some (Ir.num n1), Some (Ir.num n2)) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (N.leb n1 n2)))
    (* Comparison with poison *)
    | (Some Ir.poison, _) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    | (_, Some Ir.poison) =>
      sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison)
    (* Comparison with pointer *)
    | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
      match (icmp_ule_ptr p1 p2 (Ir.Config.m c)) with
      | Some b => sr_success Ir.e_none (update_reg_and_incrpc c r (to_num b))
      | None => sr_goes_wrong
      end
    | (_, _) => sr_goes_wrong
    end

  | _ => sr_goes_wrong (* Untyped IR *)
  end.


Definition br (c:Ir.Config.t) (bbid:nat): step_res :=
  match (Ir.Config.cur_fdef_pc c) with
  | Some (fdef, pc0) =>
    let bbid_old := pc_bbid pc0 in
    match (Ir.IRFunction.get_begin_pc_bb bbid fdef) with
    | Some pc_next =>
      sr_success Ir.e_none (Ir.Config.update_pc c pc_next)
    | None => sr_goes_wrong
    end
  | None => sr_goes_wrong
  end.

(* Semantics of terminator. *)
Definition t_step (c:Ir.Config.t) (t:Ir.Terminator.t): step_res :=
  match t with
  | Ir.Terminator.tbr bbid =>
    (* Unconditional branch. *)
    br c bbid

  | Ir.Terminator.tbr_cond condop bbid_t bbid_f =>
    (* Conditional branch. *)
    let tgt :=
        match (Ir.Config.get_val c condop) with
        | Some (Ir.num cond) =>
          if N.eqb cond 0%N then Some bbid_f
          else Some bbid_t
        | _ => None (* note that 'br poison' is UB. *)
        end in
    match tgt with
    | None => sr_goes_wrong
    | Some bbid => br c bbid
    end

  | Ir.Terminator.tret retop =>
    match (Ir.Config.get_val c retop) with
    | Some v =>
      if Ir.Config.has_nestedcall c then
        (* TODO: Will be revisited later, after 'call' instruction is added. *)
        sr_goes_wrong
      else
        sr_prog_finish v
      (* is there only one activation record in a call stack? *)
    | None => sr_goes_wrong
    end

  end.

(* Semantics of phi nodes. *)
Definition phi_step (bef_bbid:nat) (c:Ir.Config.t) (p:Ir.PhiNode.t): option Ir.Config.t :=
  match list_find_key p.(snd) bef_bbid with
  | (_, op0)::_ =>
    match Ir.Config.get_val c op0 with
    | Some v => Some (Ir.Config.update_rval c p.(fst).(fst) v)
    | None => None
    end
  | nil => None
  end.

End SmallStep.

End Ir.
Require Import List.
Require Import Bool.
Require Import BinNatDef.
Require Import Omega.
Require Import sflib.

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


Inductive step_res :=
| sr_success: Ir.event -> Ir.Config.t -> step_res
| sr_goes_wrong: step_res (* went wrong. *)
| sr_oom: step_res (* out-of-memory *)
| sr_nondet: step_res (* has non-deterministic result. *)
| sr_prog_finish: Ir.val -> step_res (* program has finished (with following integer). *)
.

(****************************************************
             Semantics of instructions.
 ****************************************************)

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

(* Semantics of an instruction which behaves deterministically.
   If running the instruction raises nondeterministic result,
   this function returns sr_goes_wrong. *)
Definition inst_det_step (c:Ir.Config.t) (i:Ir.Inst.t): step_res :=
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

  | ibitcast r opval retty =>
    match (Ir.Config.get_val c opval) with
    | Some (Ir.ptr p) =>
      match retty with
      | Ir.ptrty _ => sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.ptr p))
      | _ => sr_goes_wrong
      end
    | Some (Ir.num n) =>
      match retty with
      | Ir.ity _ => sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num n))
      | _ => sr_goes_wrong
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

(* Inductive definition of small-step semantics of instruction *)
Inductive inst_step: Ir.Config.t -> Ir.Inst.t -> step_res -> Prop :=
| s_binop: forall c i r retty bopc op1 op2
      (HINST:i = Ir.Inst.ibinop r retty bopc op1 op2),
    inst_step c i (inst_det_step c i)

| s_psub: forall c i r retty ptrty opptr1 opptr2
      (HINST:i = Ir.Inst.ipsub r retty ptrty opptr1 opptr2),
    inst_step c i (inst_det_step c i)

| s_gep: forall c i r retty opptr opidx inb
      (HINST:i = Ir.Inst.igep r retty opptr opidx inb),
    inst_step c i (inst_det_step c i)

| s_load: forall c i r retty opptr
      (HINST:i = Ir.Inst.iload r retty opptr),
    inst_step c i (inst_det_step c i)

| s_store: forall c i valty opval opptr
      (HINST:i = Ir.Inst.istore valty opval opptr),
    inst_step c i (inst_det_step c i)

| s_malloc_zero: forall c i r szty opsz
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HZERO:Ir.Config.get_val c opsz = Some (Ir.num 0%N)),
    inst_step c i (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.ptr Ir.NULL)))

| s_malloc_oom: forall c i r szty opsz nsz
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HSZ:Some (Ir.num nsz) = Ir.Config.get_val c opsz)
      (HNOSPACE:~exists (P:list nat),
            Ir.Memory.allocatable (Ir.Config.m c) (List.map (fun addr => (addr, N.to_nat nsz)) P) = true),
    inst_step c i sr_oom

| s_malloc: forall c i r szty opsz nsz (P:list nat) m' l contents
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HSZ:Some (Ir.num nsz) = Ir.Config.get_val c opsz)
      (HSZ2:N.to_nat nsz > 0)
      (HC:contents = List.repeat (Ir.Byte.poison) (N.to_nat nsz))
      (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk
                                            (Ir.heap) (begt, None) (N.to_nat nsz)
                                            (Ir.SYSALIGN) contents P))
      (HDISJ:Ir.Memory.allocatable (Ir.Config.m c)
                       (List.map (fun addr => (addr, N.to_nat nsz)) P) = true)
      (HNEW: (m', l) = Ir.Memory.new (Ir.Config.m c) (Ir.heap) (N.to_nat nsz)
                                     (Ir.SYSALIGN) contents P HMBWF HDISJ),
    inst_step c i (sr_success Ir.e_none (update_reg_and_incrpc
                                           (Ir.Config.update_m c m') r
                    (Ir.ptr (Ir.plog (l, 0)))))

| s_free: forall c i opptr
      (HINST:i = Ir.Inst.ifree opptr),
    inst_step c i (inst_det_step c i)

| s_bitcast: forall c i r opval retty
      (HINST:i = Ir.Inst.ibitcast r opval retty),
    inst_step c i (inst_det_step c i)

| s_ptrtoint: forall c i r opptr retty
      (HINST:i = Ir.Inst.iptrtoint r opptr retty),
    inst_step c i (inst_det_step c i)

| s_inttoptr: forall c i r opint retty
      (HINST:i = Ir.Inst.iinttoptr r opint retty),
    inst_step c i (inst_det_step c i)

| s_event: forall c i opval
      (HINST:i = Ir.Inst.ievent opval),
    inst_step c i (inst_det_step c i)

| s_icmp_eq_nondet: forall c i r opty op1 op2 mb1 mb2 l1 o1 l2 o2 res
      (HINST:i = Ir.Inst.iicmp_eq r opty op1 op2)
      (HOP1:Some (Ir.ptr (Ir.plog (l1, o1))) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr (Ir.plog (l2, o2))) = Ir.Config.get_val c op2)
      (HMB1:Some mb1 = Ir.Memory.get (Ir.Config.m c) l1)
      (HMB2:Some mb2 = Ir.Memory.get (Ir.Config.m c) l2)
      (HDIFF:~l1 = l2)
      (HNOTINB:~(o1 < Ir.MemBlock.n mb1 /\ o2 < Ir.MemBlock.n mb2))
      (HNONDET:res = 0%N \/ res = 1%N),
    inst_step c i (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

| s_icmp_eq: forall c i r opty op1 op2 c'
      (HINST:i = Ir.Inst.iicmp_eq r opty op1 op2)
      (HC':sr_success Ir.e_none c' = inst_det_step c i),
    inst_step c i (sr_success Ir.e_none c')

| s_icmp_ule_nondet_diff: forall c i r opty op1 op2 mb1 mb2 l1 l2 o1 o2 res
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HOP1:Some (Ir.ptr (Ir.plog (l1, o1))) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr (Ir.plog (l2, o2))) = Ir.Config.get_val c op2)
      (HMB1:Some mb1 = Ir.Memory.get (Ir.Config.m c) l1)
      (HMB2:Some mb2 = Ir.Memory.get (Ir.Config.m c) l2)
      (HDIFF:~l1 = l2)
      (HNONDET:res = 0%N \/ res = 1%N),
    inst_step c i (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

| s_icmp_ule_nondet_same: forall c i r opty op1 op2 mb l o1 o2 res
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HOP1:Some (Ir.ptr (Ir.plog (l, o1))) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr (Ir.plog (l, o2))) = Ir.Config.get_val c op2)
      (HMB:Some mb = Ir.Memory.get (Ir.Config.m c) l)
      (HNOTINB:~(o1 <= Ir.MemBlock.n mb /\ o2 <= Ir.MemBlock.n mb))
      (HNONDET:res = 0%N \/ res = 1%N),
    inst_step c i (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

| s_icmp_ule: forall c i r opty op1 op2 c'
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HC':sr_success Ir.e_none c' = inst_det_step c i),
    inst_step c i (sr_success Ir.e_none c')
.

(****************************************************
             Semantics of terminator.
 ****************************************************)
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

(****************************************************
             Semantics of phi node.
 ****************************************************)
Definition phi_step (bef_bbid:nat) (c:Ir.Config.t) (p:Ir.PhiNode.t): option Ir.Config.t :=
  match list_find_key p.(snd) bef_bbid with
  | (_, op0)::_ =>
    match Ir.Config.get_val c op0 with
    | Some v => Some (Ir.Config.update_rval c p.(fst).(fst) v)
    | None => None
    end
  | nil => None
  end.



(****************************************************
        Theorems about sstep of instruction.
 ****************************************************)

Lemma cid_to_f_In_get_funid:
  forall curcid funid0 c
         (HWF:Ir.Config.wf c)
         (HIN:In (curcid, funid0) (Ir.Config.cid_to_f c)),
    Some funid0 = Ir.Config.get_funid c curcid.
Proof.
  intros.
  inversion HWF.
  unfold Ir.Config.get_funid.
  remember (list_find_key (Ir.Config.cid_to_f c) curcid) as res.
  assert (List.length res < 2).
  { eapply list_find_key_NoDup.
    eassumption. eassumption. }
  assert (List.In (curcid, funid0) res).
  { rewrite Heqres. eapply list_find_key_In.
    eassumption. }
  destruct res; try (inversion H0; fail).
  destruct res.
  - inversion H0. rewrite H1. reflexivity. inversion H1.
  - simpl in H. omega.
Qed.

Lemma incrpc_wf:
  forall c c'
         (HWF:Ir.Config.wf c)
         (HC':c' = incrpc c),
    Ir.Config.wf c'.
Proof.
  (* High-level proof: incrpc changes stack frame only, and
     next_trivial_pc satisfies valid_pc. *) 
  intros.
  unfold incrpc in HC'.
  destruct (Ir.Config.cur_fdef_pc c) eqn:HC.
  - destruct p as [fdef pc0].
    remember (Ir.IRFunction.next_trivial_pc pc0 fdef) as pc_next.
    destruct pc_next as [pc_next | ].
    unfold Ir.Config.update_pc in HC'.
    remember (Ir.Config.s c) as s'.
    destruct s' as [ | [cid pc0'] st] .
    + congruence.
    + (* show that pc0' = pc0 *)
      unfold Ir.Config.cur_fdef_pc in HC.
      rewrite <- Heqs' in HC.
      remember (Ir.Config.get_funid c cid) as ofunid.
      destruct ofunid as [funid | ]; try (inversion HC; fail).
      remember (Ir.IRModule.getf funid (Ir.Config.md c)) as ofdef'.
      destruct ofdef' as [fdef' | ]; try (inversion HC; fail).
      inversion HC.
      rewrite H0, H1 in *.
      clear H0 H1 HC.
      (* Now prove Ir.Config.wf c' *)
      rewrite HC'.
      inversion HWF.
      split.
      * assumption.
      * assumption.
      * assumption.
      * simpl.
        intros.
        rewrite <- Heqs' in wf_stack.
        simpl in wf_stack.
        destruct HIN.
        -- inversion H. rewrite H1, H2 in *. clear H H1 H2.
           apply Ir.IRFunction.next_trivial_pc_valid with (pc1 := pc0).
           apply wf_stack with (curcid0 := curcid) (funid := funid0).
           left. reflexivity.
           eassumption. assumption.
           assert (HINCID:Some funid0 = Ir.Config.get_funid c curcid).
           { apply cid_to_f_In_get_funid. assumption. assumption. }
           rewrite <- Heqofunid in HINCID.
           inversion HINCID.
           rewrite H0 in HF. rewrite <- HF in Heqofdef'.
           inversion Heqofdef'. rewrite <- H1. congruence.
         -- apply wf_stack with (curcid := curcid) (funid := funid0).
            right. assumption. assumption. assumption.
    + congruence.
  - congruence.
Qed.

Lemma update_rval_wf:
  forall c c' r v
         (HWF:Ir.Config.wf c)
         (HC':c' = Ir.Config.update_rval c r v),
    Ir.Config.wf c'.
Proof.
  intros.
  inversion HWF.
  unfold Ir.Config.update_rval in HC'.
  rewrite HC'.
  split; try assumption.
Qed.

Lemma update_reg_and_incrpc_wf:
  forall c c' v r
         (HWF:Ir.Config.wf c)
         (HC':c' = update_reg_and_incrpc c r v),
    Ir.Config.wf c'.
Proof.
  intros.
  unfold update_reg_and_incrpc in HC'.
  assert (Ir.Config.wf (Ir.Config.update_rval c r v)).
  { eapply update_rval_wf. eassumption. reflexivity. }
  rewrite HC'.
  eapply incrpc_wf.
  eapply H. reflexivity.  
Qed.


Ltac thats_it := eapply update_reg_and_incrpc_wf; eauto.
Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).


(* Theorem: inst_step preserves well-formedness of configuration. *)
Theorem inst_step_wf:
  forall c i c' e
         (HWF:Ir.Config.wf c)
         (HSTEP:inst_step c i (sr_success e c')),
    Ir.Config.wf c'.
Proof.
  intros.
  inversion HSTEP.
  - (* ibinop. *)
    rewrite HINST in H2.
    destruct bopc.
    { simpl in H2.
      destruct retty; try (inversion H2; fail).
      des_op c op1 opv1 H2. des_op c op2 opv2 H2.
      + destruct opv1; try (inversion H2; fail);
          destruct opv2; try (inversion H2; fail);
            inversion H2; thats_it.
      + destruct opv1; try (inversion H2; fail).
    }
    { simpl in H2.
      destruct retty; try (inversion H2; fail).
      des_op c op1 opv1 H2. des_op c op2 opv2 H2.
      + destruct opv1; try (inversion H2; fail);
          destruct opv2; try (inversion H2; fail);
            inversion H2; thats_it.
      + destruct opv1; try (inversion H2; fail).
    }
  - (* ipsub. *)
    rewrite HINST in H2.
    simpl in H2.
    destruct retty; try (inversion H2; fail).
    destruct ptrty; try (inversion H2; fail).
    des_op c opptr1 op1 H2.
    destruct (op1) as [n1 | p1 | ]; try (inversion H2; fail).
    + des_op c opptr2 op2 H2.
      destruct (op2) as [n2 | p2 | ]; try (inversion H2; fail);
      inversion H2; thats_it.
    + des_op c opptr2 op2 H2.
      destruct (op2) as [n2 | p2 | ]; try (inversion H2; fail);
      inversion H2. thats_it.
  - (* igep. *)
    rewrite HINST in H2.
    simpl in H2.
    destruct retty; try (inversion H2; fail).
    des_op c opptr op1 H2.
    destruct (op1) as [n1 | ptr | _]; try (inversion H2; fail).
    + des_op c opidx op2 H2.
      destruct (op2) as [idx | ptr2 | _]; try (inversion H2; fail);
        inversion H2; thats_it.
    + des_op c opidx op2 H2.
      destruct (op2) as [idx | ptr2 | _]; try (inversion H2; fail).
        inversion H2; thats_it.
  - (* iload. *)
    rewrite HINST in H2.
    simpl in H2.
    des_op c opptr op1 H2.
    destruct op1; try (inversion H2; fail).
    des_ifH H2; try (inversion H2; fail).
    inversion H2. thats_it.
  - (* istore. *)
    rewrite HINST in H2.
    simpl in H2.
    des_op c opval opv H2.
    destruct opv; try (inversion H2; fail).
    des_op c opptr opp H2.
    destruct (Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz valty)) eqn:Hderef;
      try (inversion H2; fail).
    inversion H2.
    apply incrpc_wf with (c := Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p opp valty));
      try reflexivity.
    destruct HWF.
    split; simpl; try assumption.
    eapply Ir.store_val_wf. eassumption. reflexivity.  congruence.
  - (* imalloc with size 0 *)
    thats_it.
  - (* imalloc, succeed *)
    eapply update_reg_and_incrpc_wf with (c := Ir.Config.update_m c m').
    + inversion HWF.
      split.
      * simpl. eapply Ir.Memory.new_wf.
        eapply wf_m.
        eapply HNEW.
      * simpl. assumption.
      * simpl. assumption.
      * simpl. assumption.
    + reflexivity.
  - (* ifree *)
    destruct HWF.
    rewrite HINST in H2.
    simpl in H2.
    des_op c opptr opp H2.
    destruct opp; try (inversion H2; fail).
    destruct (free p (Ir.Config.m c)) as [m0 | ] eqn:Hfree; try (inversion H2; fail).
    inversion H2.
    unfold free in Hfree.
    destruct p.
    + destruct p. destruct n; try (inversion Hfree).
      apply incrpc_wf with (c := Ir.Config.update_m c m0).
      assert (HWF':Ir.Memory.wf m0).
      { eapply Ir.Memory.free_wf. eapply wf_m. erewrite Hfree. reflexivity. }
      split; try (simpl; assumption). reflexivity.
    + destruct p. destruct p.
      destruct (Ir.Memory.zeroofs_block (Ir.Config.m c) n) eqn:Hblk.
      * destruct p.
        des_ifH Hfree.
        apply incrpc_wf with (c := Ir.Config.update_m c m0).
        assert (HWF':Ir.Memory.wf m0).
        { eapply Ir.Memory.free_wf. eapply wf_m. erewrite Hfree. reflexivity. }
        split; try (simpl; assumption). reflexivity.
        inversion Hfree.
      * inversion Hfree.
  - (* ibitcast. *)
    rewrite HINST in H2. simpl in H2.
    des_op c opval opv H2.
    destruct opv; try (inversion H2; fail).
    + destruct retty; try (inversion H2; fail).
      inversion H2; thats_it.
    + destruct retty; try (inversion H2; fail).
      inversion H2; thats_it.
  - (* iptrtoint. *)
    rewrite HINST in H2. simpl in H2.
    destruct retty; try (inversion H2; fail).
    des_op c opptr opp H2.
    destruct opp; try (inversion H2; fail);
    inversion H2; thats_it.
  - (* iinttoptr *)
    rewrite HINST in H2. simpl in H2.
    destruct retty; try (inversion H2; fail).
    des_op c opint opi H2.
    destruct opi; try (inversion H2; fail);
    inversion H2; thats_it.
  - (* ievent *)
    rewrite HINST in H2. simpl in H2.
    des_op c opval opv H2.
    destruct opv; try (inversion H2; fail).
    inversion H2. eapply incrpc_wf. eassumption. reflexivity.
  - (* iicmp_eq, nondet *)
    eapply update_reg_and_incrpc_wf.
    eassumption.
    reflexivity.
  - (* iicmp_eq, det *)
    rewrite HINST in HC'. simpl in HC'.
    des_op c op1 op1v HC'.
    + destruct op1v.
      * des_op c op2 op2v HC'.
        destruct op2v; inversion HC'; thats_it.
      * des_op c op2 op2v HC'.
        destruct op2v; try (inversion HC'; fail).
        destruct (icmp_eq_ptr p p0 (Ir.Config.m c)) eqn:Heq_ptr; try (inversion HC'; fail);
        inversion HC'; thats_it.
        inversion HC'. thats_it.
      * inversion HC'. thats_it.
    + des_op c op2 op2v HC'.
      destruct op2v; try (inversion HC'; fail).
      inversion HC'. thats_it.
  - (* icmp_ule, nondet *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
  - (* icmp_ule, nondet 2 *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
  - (* icmp_ule, det *)
    rewrite HINST in HC'. simpl in HC'.
    des_op c op1 op1v HC'.
    + destruct op1v; try (inversion HC'; fail);
      des_op c op2 op2v HC'.
      * destruct op2v; try (inversion HC'; fail);
        inversion HC'; thats_it.
      * destruct op2v; try (inversion HC'; fail).
        -- destruct (icmp_ule_ptr p p0 (Ir.Config.m c)) eqn:Huleptr; try (inversion HC'; fail).
           inversion HC'. thats_it.
        -- inversion HC'. thats_it.
      * inversion HC'. thats_it.
      * inversion HC'. thats_it.
    + des_op c op2 op2v HC'.
      destruct op2v; try (inversion HC'; fail).
      inversion HC'. thats_it.
Qed.

End SmallStep.

End Ir.
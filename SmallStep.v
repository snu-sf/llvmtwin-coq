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

Section SMALLSTEP.

Import Ir.Inst.
Variable md:Ir.IRModule.t.

(* Returns basic block id of pc *)
Definition pc_bbid (p:Ir.IRFunction.pc): nat :=
  match p with
  | Ir.IRFunction.pc_phi bbid _ => bbid
  | Ir.IRFunction.pc_inst bbid _ => bbid
  end.

(* Increment pc of the config. *)
Definition incrpc (c:Ir.Config.t) :=
  match (Ir.Config.cur_fdef_pc md c) with
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


(* Definition of the result after a step. *)
Inductive step_res :=
| sr_success: Ir.event -> Ir.Config.t -> step_res
| sr_goes_wrong: step_res (* went wrong. *)
| sr_oom: step_res (* out-of-memory *)
| sr_prog_finish: Ir.val -> step_res (* program has finished (with a return value). *)
.


(****************************************************
             Semantics of instructions.
 ****************************************************)

(* Convert a pointer into N. *)
Definition p2N (p:Ir.ptrval) (m:Ir.Memory.t) (sz:nat):N :=
  match p with
  | Ir.plog l o =>
    match Ir.log_to_phy m l o with
    | Some (Ir.pphy o' _ _) =>
      twos_compl2 o' sz
    | _ => 0%N
    end
  | Ir.pphy o _ _ =>
    twos_compl2 o sz
  end.

(* Pointer subtraction. *)
Definition psub p1 p2 m bsz :=
  let s := N.shiftl 2%N (N.of_nat bsz) in
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    if Nat.eqb l1 l2 then
      Ir.num (twos_compl_sub (N.of_nat o1) (N.of_nat o2) bsz)
    else Ir.poison
  | (Ir.pphy o1 _ _, Ir.plog _ _) =>
    Ir.num (twos_compl_sub (N.of_nat o1) (p2N p2 m bsz) bsz)
  | (Ir.plog _ _, Ir.pphy o2 _ _) =>
    Ir.num (twos_compl_sub (p2N p1 m bsz) (N.of_nat o2) bsz)
  | (Ir.pphy o1 _ _, Ir.pphy o2 _ _) =>
    Ir.num (twos_compl_sub (N.of_nat o1) (N.of_nat o2) bsz)
  end.

(* getelementptr with/without inbounds tag. *)
Definition gep (p:Ir.ptrval) (idx0:N) (t:Ir.ty) (m:Ir.Memory.t) (inb:bool): Ir.val :=
  let idx := N.mul idx0 (N.of_nat (Ir.ty_bytesz t)) in
  match p with
  | Ir.plog l o =>
    let o' := N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ) in
    if inb then
      match (Ir.Memory.get m l) with
      | Some blk =>
        if Ir.MemBlock.inbounds o blk &&
           Ir.MemBlock.inbounds o' blk then Ir.ptr (Ir.plog l o')
        else Ir.poison (* out of bounds *)
      | None => Ir.poison (* unreachable *)
      end
    else Ir.ptr (Ir.plog l o')
  | Ir.pphy o Is cid =>
    let o' := N.to_nat (twos_compl_add (N.of_nat o) idx Ir.PTRSZ) in
    if inb then
      if N.ltb idx (N.shiftl 1 (N.sub (N.of_nat Ir.PTRSZ) 1%N)) then
        (* Added idx is positive. *)
        if Nat.ltb o' Ir.MEMSZ then
          (* Should not overflow Ir.MEMSZ *)
          Ir.ptr (Ir.pphy o' (o::o'::Is) cid)
        else Ir.poison
      else
        (* idx is negative: no constraint. *)
        Ir.ptr (Ir.pphy o' (o::o'::Is) cid)
    else
      Ir.ptr (Ir.pphy o' Is cid)
  end.

(* free operation. *)
Definition free p m: option (Ir.Memory.t) :=
  match p with
  | Ir.plog l 0 => Ir.Memory.free m l
  | Ir.pphy o Is cid =>
    match (Ir.Memory.zeroofs_block m o) with
    | None => None
    | Some (bid, mb) =>
      if Ir.deref m p 1 then (* to use Is, cid info *)
        Ir.Memory.free m bid
      else None
    end
  | _ => None
  end.

Definition icmp_eq_ptr_nondet_cond (p1 p2:Ir.ptrval) (m:Ir.Memory.t): bool :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
    | (Some mb1, Some mb2) =>
      (negb (Nat.eqb l1 l2)) &&
      ((Nat.eqb o1 mb1.(Ir.MemBlock.n) && Nat.eqb o2 0) ||
       (mb1.(Ir.MemBlock.n) <? o1) ||
       (Nat.eqb o1 0 && Nat.eqb o2 mb2.(Ir.MemBlock.n)) ||
       (mb2.(Ir.MemBlock.n) <? o2) ||
       (* even if offsets are inbounds, comparison result is nondeterministic
          if lifetimes are disjoint. *)
       (match (mb1.(Ir.MemBlock.r), mb2.(Ir.MemBlock.r)) with
        | ((b1, None), (b2, None)) => false
        | ((b1, None), (b2, Some e2)) => e2 <? b1
        | ((b1, Some e1), (b2, None)) => e1 <? b2
        | ((b1, Some e1), (b2, Some e2)) => (e1 <? b2) || (e2 <? b1)
        end))
    | (_, _) => false
    end
  | (_, _) => false
  end.

(* p1 == p2 *)
Definition icmp_eq_ptr (p1 p2:Ir.ptrval) (m:Ir.Memory.t): option bool :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    if Nat.eqb l1 l2 then
      (* ICMP-PTR-LOGICAL *)
      Some (Nat.eqb o1 o2)
    else
      if icmp_eq_ptr_nondet_cond p1 p2 m then None
      else Some false
  | (Ir.pphy o1 Is1 cid1, _) =>
    Some (N.eqb (N.of_nat o1) (p2N p2 m Ir.PTRSZ))
  | (_, Ir.pphy o2 Is2 cid2) =>
    Some (N.eqb (p2N p1 m Ir.PTRSZ) (N.of_nat o2))
  end.

(* p1 <= p2 *)
Definition icmp_ule_ptr (p1 p2:Ir.ptrval) (m:Ir.Memory.t): option bool :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    if Nat.eqb l1 l2 then
      match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
      | (Some mb1, Some mb2) =>
        if Nat.leb o1 (Ir.MemBlock.n mb1) && Nat.leb o2 (Ir.MemBlock.n mb2) then
          Some (Nat.leb o1 o2)
        else None (* nondet. value *)
      | (_, _) => None
      end
    else None (* nondet. value *)
  | (Ir.pphy o1 Is1 cid1, _) =>
    Some (N.leb (N.of_nat o1) (p2N p2 m Ir.PTRSZ))
  | (_, Ir.pphy o2 Is2 cid2) =>
    Some (N.leb (p2N p1 m Ir.PTRSZ) (N.of_nat o2))
  end.

Definition binop (bopc:Ir.Inst.bopcode) (i1 i2:N) (bsz:nat):N :=
  match bopc with
  | Ir.Inst.bop_add => twos_compl_add i1 i2 bsz
  | Ir.Inst.bop_sub => twos_compl_sub i1 i2 bsz
  end.

(* Semantics of an instruction which behaves deterministically.
   If IR module of c is well-typed, and this function returns Some (result),
   there is no possible execution other than the result.
   If running the instruction raises nondeterministic result,
   this function returns None. *)
Definition inst_det_step (c:Ir.Config.t): option step_res :=
  match (Ir.Config.cur_inst md c) with
  | Some i =>
    match i with
    | ibinop r opty bopc op1 op2 =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match opty with
        | Ir.ity bsz =>
          match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
          | (Some (Ir.num i1), Some (Ir.num i2)) => Ir.num (binop bopc i1 i2 bsz)
          | (_, _) => Ir.poison
          end
        | _ => Ir.poison
        end))

    | ipsub r retty ptrty op1 op2 =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match (retty, ptrty) with
        | (Ir.ity bsz, Ir.ptrty opty) =>
          match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
          | (Some (Ir.ptr p1), Some (Ir.ptr p2)) => psub p1 p2 (Ir.Config.m c) bsz
          | (_, _) => Ir.poison
          end
        | (_, _) => Ir.poison
        end))

    | igep r ptrty opptr opidx inb =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match ptrty with
        | Ir.ptrty retty =>
          match (Ir.Config.get_val c opptr, Ir.Config.get_val c opidx) with
          | (Some (Ir.ptr p), Some (Ir.num idx)) => gep p idx retty (Ir.Config.m c) inb
          | (_, _) => Ir.poison
          end
        | _ => Ir.poison
        end))

    | iload r retty opptr =>
      match (Ir.Config.get_val c opptr) with
      | (Some (Ir.ptr p)) =>
        if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz retty) then
          Some (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.load_val (Ir.Config.m c) p retty)))
        else Some sr_goes_wrong
      | _ => (* type check fail *)
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison))
      end

    | istore valty opptr opval =>
      match (Ir.Config.get_val c opptr, Ir.Config.get_val c opval) with
      | (Some (Ir.ptr p), Some v) =>
        if Ir.deref (Ir.Config.m c) p (Ir.ty_bytesz valty) then
          Some (sr_success Ir.e_none
                           (incrpc (Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty))))
        else Some sr_goes_wrong
      | (_, _) => (* type check fail *)
        Some (sr_success Ir.e_none (incrpc c))
      end

    | imalloc r opty opval =>
      (* malloc is not determinstic! *)
      None

    | ifree opptr =>
      match (Ir.Config.get_val c opptr) with
      | Some (Ir.ptr p) =>
        match (free p (Ir.Config.m c)) with
        | Some m => Some (sr_success Ir.e_none (incrpc (Ir.Config.update_m c m)))
        | None => Some sr_goes_wrong
        end
      | _ => Some sr_goes_wrong
      end

    | ibitcast r opval retty =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match (Ir.Config.get_val c opval) with
        | Some (Ir.ptr p) =>
          match retty with
          | Ir.ptrty _ => Ir.ptr p
          | _ => Ir.poison
          end
        | Some (Ir.num n) =>
          match retty with
          | Ir.ity _ => Ir.num n
          | _ => Ir.poison
          end
        | _ => Ir.poison
        end))

    | iptrtoint r opptr retty =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match retty with
        | Ir.ity retty =>
          match (Ir.Config.get_val c opptr) with
          | Some (Ir.ptr p) => Ir.num (p2N p (Ir.Config.m c) retty)
          | _ => Ir.poison
          end
        | _ => Ir.poison
        end))

    | iinttoptr r opint retty =>
      Some (sr_success Ir.e_none (update_reg_and_incrpc c r
        match retty with
        | Ir.ptrty retty =>
          match (Ir.Config.get_val c opint) with
          | Some (Ir.num n) => Ir.ptr (Ir.pphy (N.to_nat n) nil None)
          | _ => Ir.poison
          end
        | _ => Ir.poison
        end))

    | ievent opval =>
      match (Ir.Config.get_val c opval) with
      | Some (Ir.num n) => Some (sr_success (Ir.e_some n) (incrpc c))
      | _ => Some sr_goes_wrong
      end

    | iicmp_eq r opty op1 op2 =>
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      (* Integer comparison *)
      | (Some (Ir.num n1), Some (Ir.num n2)) =>
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (N.eqb n1 n2))))
      (* Pointer comparison *)
      | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
        match (icmp_eq_ptr p1 p2 (Ir.Config.m c)) with
        | Some b => Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num b)))
        | None => None (* nondet. result *)
        end
      | (_, _) => (* In other cases, it is untyped. *)
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison))
      end

    | iicmp_ule r opty opptr1 opptr2 =>
      match (Ir.Config.get_val c opptr1, Ir.Config.get_val c opptr2) with
      (* Integer comparison *)
      | (Some (Ir.num n1), Some (Ir.num n2)) =>
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (N.leb n1 n2))))
      (* Comparison with pointer *)
      | (Some (Ir.ptr p1), Some (Ir.ptr p2)) =>
        match (icmp_ule_ptr p1 p2 (Ir.Config.m c)) with
        | Some b => Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num b)))
        | None => None
        end
      | (_, _) => (* In other cases, it is untyped. *)
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r Ir.poison))
      end
    end

  | None => Some sr_goes_wrong
  end.

(* Inductive definition of small-step semantics of instruction.
   Note that sr_nondet is never used in inst_step. *)
Inductive inst_step: Ir.Config.t -> step_res -> Prop :=
| s_det: forall c sr
      (HNEXT:Some sr = inst_det_step c), inst_step c sr

| s_malloc_zero: forall c i r szty opsz
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HZERO:Ir.Config.get_val c opsz = Some (Ir.num 0%N)),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.ptr Ir.NULL)))

| s_malloc_oom: forall c i r szty opsz nsz
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HSZ:Some (Ir.num nsz) = Ir.Config.get_val c opsz)
      (HNOSPACE:~exists (P:list nat),
            Ir.Memory.allocatable (Ir.Config.m c) (List.map (fun addr => (addr, N.to_nat nsz)) P) = true),
    inst_step c sr_oom

| s_malloc: forall c i r szty opsz nsz (P:list nat) m' l contents
      (HCUR:Some i = Ir.Config.cur_inst md c)
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
                                     (Ir.SYSALIGN) contents P),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc
                                           (Ir.Config.update_m c m') r
                    (Ir.ptr (Ir.plog l 0))))

| s_icmp_eq_nondet: forall c i r opty op1 op2 p1 p2 res
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.iicmp_eq r opty op1 op2)
      (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr p2) = Ir.Config.get_val c op2)
      (HNONDET:icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m c) = true),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

| s_icmp_ule_nondet_diff: forall c i r opty op1 op2 mb1 mb2 l1 l2 o1 o2 res
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HOP1:Some (Ir.ptr (Ir.plog l1 o1)) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr (Ir.plog l2 o2)) = Ir.Config.get_val c op2)
      (HMB1:Some mb1 = Ir.Memory.get (Ir.Config.m c) l1)
      (HMB2:Some mb2 = Ir.Memory.get (Ir.Config.m c) l2)
      (HDIFF:~l1 = l2)
      (HNONDET:res = 0%N \/ res = 1%N),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

| s_icmp_ule_nondet_same: forall c i r opty op1 op2 mb l o1 o2 res
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HOP1:Some (Ir.ptr (Ir.plog l o1)) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr (Ir.plog l o2)) = Ir.Config.get_val c op2)
      (HMB:Some mb = Ir.Memory.get (Ir.Config.m c) l)
      (HNOTINB:~(o1 <= Ir.MemBlock.n mb /\ o2 <= Ir.MemBlock.n mb))
      (HNONDET:res = 0%N \/ res = 1%N),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))
.

(* Result of N small steps on instructions. *)
Inductive inst_nstep: Ir.Config.t -> nat -> Ir.trace * step_res -> Prop :=
| ns_one: forall c sr (HSINGLE:inst_step c sr),
    inst_nstep c 1 (nil, sr)
| ns_success: forall c n c' tr e sr
           (HSUCC: inst_nstep c n (tr, sr_success e c'))
           (HSINGLE: inst_step c' sr),
      inst_nstep c (S n) (e::tr, sr)
| ns_oom: forall c n tr (HOOM: inst_nstep c n (tr, sr_oom)),
    inst_nstep c (S n) (tr, sr_oom)
| ns_goes_wrong: forall c n tr (HGW: inst_nstep c n (tr, sr_goes_wrong)),
    inst_nstep c (S n) (tr, sr_goes_wrong).



(* Categorization of instructions. *)
Definition changes_mem (i:Ir.Inst.t): bool :=
  match i with
  | ibinop _ _ _ _ _ => false
  | ipsub _ _ _ _ _ => false
  | igep _ _ _ _ _ => false
  | iload _ _ _ => false
  | istore _ _ _ => true
  | imalloc _ _ _ => true
  | ifree _ => true
  | ibitcast _ _ _ => false
  | iptrtoint _ _ _ => false
  | iinttoptr _ _ _ => false
  | ievent _ => false
  | iicmp_eq _ _ _ _ => false
  | iicmp_ule _ _ _ _ => false
  end.
Definition never_goes_wrong (i:Ir.Inst.t): bool :=
  match i with
  | ibinop _ _ _ _ _ => true
  | ipsub _ _ _ _ _ => true
  | igep _ _ _ _ _ => true
  | iload _ _ _ => false
  | istore _ _ _ => false
  | imalloc _ _ _ => true
  | ifree _ => false
  | ibitcast _ _ _ => true
  | iptrtoint _ _ _ => true
  | iinttoptr _ _ _ => true
  | ievent _ => false
  | iicmp_eq _ _ _ _ => true
  | iicmp_ule _ _ _ _ => true
  end.
Definition allocates_mem (i:Ir.Inst.t): bool :=
  match i with
  | imalloc _ _ _ => true
  | _ => false
  end.
Definition raises_event (i:Ir.Inst.t): bool :=
  match i with
  | ibinop _ _ _ _ _ => false
  | ipsub _ _ _ _ _ => false
  | igep _ _ _ _ _ => false
  | iload _ _ _ => false
  | istore _ _ _ => false
  | imalloc _ _ _ => false
  | ifree _ => false
  | ibitcast _ _ _ => false
  | iptrtoint _ _ _ => false
  | iinttoptr _ _ _ => false
  | ievent _ => true
  | iicmp_eq _ _ _ _ => false
  | iicmp_ule _ _ _ _ => false
  end.

(****************************************************
             Semantics of terminator.
 ****************************************************)
Definition br (c:Ir.Config.t) (bbid:nat): step_res :=
  match (Ir.Config.cur_fdef_pc md c) with
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


Lemma incrpc_wf:
  forall c c'
         (HWF:Ir.Config.wf md c)
         (HC':c' = incrpc c),
    Ir.Config.wf md c'.
Proof.
  (* High-level proof: incrpc changes stack frame only, and
     next_trivial_pc satisfies valid_pc. *) 
  intros.
  unfold incrpc in HC'.
  destruct (Ir.Config.cur_fdef_pc md c) eqn:HC.
  - destruct p as [fdef pc0].
    remember (Ir.IRFunction.next_trivial_pc pc0 fdef) as pc_next.
    destruct pc_next as [pc_next | ].
    unfold Ir.Config.update_pc in HC'.
    remember (Ir.Config.s c) as s'.
    destruct s' as [ | [cid [pc0' r0']] st] .
    + congruence.
    + (* show that pc0' = pc0 *)
      unfold Ir.Config.cur_fdef_pc in HC.
      rewrite <- Heqs' in HC.
      remember (Ir.Config.get_funid c cid) as ofunid.
      destruct ofunid as [funid | ]; try (inversion HC; fail).
      remember (Ir.IRModule.getf funid md) as ofdef'.
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
        -- inversion H. rewrite H1, H2, H3 in *. clear H H1 H2 H3.
           apply Ir.IRFunction.next_trivial_pc_valid with (pc1 := pc0).
           apply wf_stack with (curcid0 := curcid) (funid := funid0) (curregfile0 := curregfile).
           left. reflexivity.
           eassumption. assumption.
           assert (HINCID:Some funid0 = Ir.Config.get_funid c curcid).
           { eapply Ir.Config.cid_to_f_In_get_funid. eassumption. assumption. }
           rewrite <- Heqofunid in HINCID.
           inversion HINCID.
           rewrite H0 in HF. rewrite <- HF in Heqofdef'.
           inversion Heqofdef'. rewrite <- H1. congruence.
         -- apply wf_stack with (curcid := curcid) (funid := funid0) (curregfile := curregfile).
            right. assumption. assumption. assumption.
      * simpl. intros. apply wf_no_bogus_ptr with (op := op) (ofs := ofs).
        unfold Ir.Config.get_val in HGETVAL.
        unfold Ir.Config.get_rval in HGETVAL. simpl in HGETVAL.
        unfold Ir.Config.get_val. unfold Ir.Config.get_rval.
        rewrite <- Heqs'. assumption.
      * simpl. intros. eapply wf_no_bogus_ptr_mem.
        eassumption.
    + congruence.
  - congruence.
Qed.

Lemma update_rval_wf:
  forall c c' r v
         (HWF:Ir.Config.wf md c)
         (HC':c' = Ir.Config.update_rval c r v)
         (HNOBOGUSPTR:forall l o (HPTR:v = Ir.ptr (Ir.plog l o)),
             l < c.(Ir.Config.m).(Ir.Memory.fresh_bid)),
    Ir.Config.wf md c'.
Proof.
  intros.
  inversion HWF.
  unfold Ir.Config.update_rval in HC'.
  rewrite HC'. clear HC'.
  destruct (Ir.Config.s c) as [ | [cid0 [pc0 reg0]] s'] eqn:Hs.
  { split; try assumption.
    intros. rewrite Hs in HIN. inversion HIN. }
  { split; try (simpl; assumption).
    simpl. intros.
    destruct HIN.
    - inversion H.
      destruct curregfile; inversion H3.
      rewrite H1, H2 in *. clear H1 H2.
      eapply wf_stack with (curcid0 := curcid). simpl. left. reflexivity.
      eassumption. assumption.
    - eapply wf_stack.
      simpl. right. eassumption. eassumption. assumption.
    - simpl. intros.
      unfold Ir.Config.get_val in HGETVAL.
      unfold Ir.Config.get_rval in HGETVAL.
      simpl in HGETVAL.
      destruct op eqn:Hop.
      + apply wf_no_bogus_ptr with (op := Ir.opconst c0) (ofs := ofs).
        des_ifs.
      + destruct (Nat.eqb r r0) eqn:Hreg.
        { apply HNOBOGUSPTR with (o := ofs).
          unfold Ir.Regfile.get in HGETVAL.
          unfold Ir.Regfile.update in HGETVAL.
          simpl in HGETVAL. rewrite Hreg in HGETVAL.
          inv HGETVAL. reflexivity. }
        { unfold Ir.Regfile.get in HGETVAL.
          unfold Ir.Regfile.update in HGETVAL.
          simpl in HGETVAL. rewrite Hreg in HGETVAL.
          apply wf_no_bogus_ptr with (op := Ir.opreg r0) (ofs := ofs).
          unfold Ir.Config.get_val.
          unfold Ir.Config.get_rval. rewrite Hs. unfold Ir.Regfile.get.
          assumption.
        }
  }
Qed.

Lemma update_reg_and_incrpc_wf:
  forall c c' v r
         (HWF:Ir.Config.wf md c)
         (HC':c' = update_reg_and_incrpc c r v)
         (HNOBOGUSPTR:forall l o (HPTR:v = Ir.ptr (Ir.plog l o)),
             l < c.(Ir.Config.m).(Ir.Memory.fresh_bid)),
    Ir.Config.wf md c'.
Proof.
  intros.
  unfold update_reg_and_incrpc in HC'.
  assert (Ir.Config.wf md (Ir.Config.update_rval c r v)).
  { eapply update_rval_wf. eassumption. reflexivity. eassumption. }
  rewrite HC'.
  eapply incrpc_wf.
  eapply H. reflexivity.
Qed.

Lemma fresh_bid_store_val:
  forall m p v t,
    Ir.Memory.fresh_bid (Ir.store_val m p v t) =
    Ir.Memory.fresh_bid m.
Proof.
  intros.
  unfold Ir.store_val. unfold Ir.store_bytes.
  unfold Ir.Memory.set.
  des_ifs.
Qed.

Ltac thats_it := eapply update_reg_and_incrpc_wf; eauto.
Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).
Ltac try_wf :=
  des_ifs; try (eapply update_reg_and_incrpc_wf; try eassumption;
                try reflexivity; try congruence; fail).

(* Lemma: inst_det_step preserves well-formedness of configuration. *)
Lemma inst_det_step_wf:
  forall c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNEXT:Some (sr_success e c') = inst_det_step c),
    Ir.Config.wf md c'.
Proof.
    intros.
    unfold inst_det_step in HNEXT. (* ibinop. *)
    rewrite <- HCUR in HNEXT.
    destruct i as [r retty bopc op1 op2 (* ibinop *)
                  |r retty ptrty opptr1 opptr2 (* ipsub *)
                  |r retty opptr opidx inb (* igep *)
                  |r retty opptr (* iload *)
                  |valty opval opptr (* istore *)
                  |(* imalloc *)
                  |opptr (* ifree *)
                  |r opval retty (* ibitcast *)
                  |r opptr retty (* iptrtoint *)
                  |r opint retty (* iinttoptr *)
                  |opval (* ievent *)
                  |r opty op1 op2 (* iicmp_eq *)
                  |r opty op1 op2 (* iicmp_ule *)
                  ] eqn:HINST; try (inversion HNEXT; fail).
    + destruct bopc; try_wf.
    + (* ipsub. *) unfold psub in HNEXT. try_wf.
    + (* igep. *) try_wf.
      eapply update_reg_and_incrpc_wf.
      eassumption. reflexivity.
      intros. unfold gep in HPTR. des_ifs.
      apply Ir.Memory.get_fresh_bid with (mb := t1). inv HWF. assumption.
      assumption.
      inv HWF. eapply wf_no_bogus_ptr. eassumption.
    + (* iload. *) try_wf.
      eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
      intros. inv HWF. eapply wf_no_bogus_ptr_mem.
      eassumption.
    + (* istore. *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty)).
      destruct HWF.
      split; simpl; try assumption. eapply Ir.store_val_wf. eassumption. reflexivity. congruence.
      intros. rewrite fresh_bid_store_val. eapply wf_no_bogus_ptr. eassumption.
      admit. (* store_val does not hamper wf_no_bogus_ptr_mem! *)
      reflexivity.
    + (* ifree *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c t0); try reflexivity.
      unfold free in Heq0.
      destruct HWF.
      des_ifs.
      * split. eapply Ir.Memory.free_wf. eassumption. rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_stack with (curcid := curcid) (funid := funid) (curregfile := curregfile).
        assumption. unfold Ir.Config.cid_to_f in *.
        unfold Ir.Config.update_m in HIN2. destruct c. simpl in *. assumption.
        assumption.
        admit. (* wf_no_bogus_ptr *)
        admit. (* wf_no_bogus_ptr_mem *)
      * split. eapply Ir.Memory.free_wf. eassumption. rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_stack with (curcid := curcid) (funid := funid) (curregfile := curregfile).
        assumption. unfold Ir.Config.cid_to_f in *.
        unfold Ir.Config.update_m in HIN2. destruct c. simpl in *. assumption.
        assumption.
        admit. (* wf_no_bogus_ptr *)
        admit. (* wf_no_bogus_ptr_mem *)
(*    + (* ibitcast. *) try_wf.
    + (* iptrtoint. *) try_wf.
    + (* iinttoptr *) try_wf.
    + (* ievent *)
      rename HNEXT into H2. simpl in H2.
      des_op c opval opv H2. des_inv opv H2.
      inversion H2. eapply incrpc_wf. eassumption. reflexivity.
    + (* iicmp_eq, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { destruct op1v.
        - des_op c op2 op2v HC'.
          destruct op2v; inversion HC'; thats_it. inv HC'. try_wf.
        - des_op c op2 op2v HC'.
          destruct op2v; try (inversion HC'; fail).
          inv HC'. try_wf.
          destruct (icmp_eq_ptr p p0 (Ir.Config.m c)) eqn:Heq_ptr; try (inversion HC'; fail);
             inversion HC'; thats_it.
          inversion HC'. thats_it.
          inv HC'. try_wf.
        - inversion HC'. thats_it. }
      { des_op c op2 op2v HC'.
        destruct op2v; try (inversion HC'; fail).
        inversion HC'. thats_it.
        inv HC'. try_wf. inv HC'. try_wf. inv HC'. try_wf.
      }
    + (* iicmp_ule, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { des_inv op1v HC';
          des_op c op2 op2v HC'; try (inv HC'; try_wf).
      }
      { des_ifs; try_wf. }
Qed.*)
Admitted.

(* Theorem: inst_step preserves well-formedness of configuration. *)
Theorem inst_step_wf:
  forall c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:inst_step c (sr_success e c')),
    Ir.Config.wf md c'.
(*Proof.
  intros.
  inversion HSTEP.
  - unfold inst_det_step in HNEXT.
    destruct (Ir.Config.cur_inst md c) as [i0|] eqn:Hcur.
    eapply inst_det_step_wf. eassumption.
    rewrite Hcur. reflexivity. unfold inst_det_step.
    rewrite Hcur. eassumption.
    inversion HNEXT.
  - (* imalloc with size 0 *)
    thats_it.
  - (* imalloc, succeed *)
    eapply update_reg_and_incrpc_wf with (c := Ir.Config.update_m c m').
    + inversion HWF.
      split; try (simpl; assumption).
      * simpl. eapply Ir.Memory.new_wf.
        eapply wf_m.
        eassumption.
        eassumption.
        eassumption.
    + reflexivity.
  - (* iicmp_eq, nondet *)
    eapply update_reg_and_incrpc_wf.
    eassumption.
    reflexivity.
  - (* icmp_ule, nondet *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
  - (* icmp_ule, nondet 2 *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
Qed.*)
Admitted.

(****************************************************
   Theorems regarding categorization of instruction.
 ****************************************************)

Lemma no_mem_change_after_incrpc:
  forall c,
    Ir.Config.m c = Ir.Config.m (incrpc c).
Proof.
  intros.
  unfold incrpc.
  destruct (Ir.Config.cur_fdef_pc md c).
  destruct p.
  { des_ifs. unfold Ir.Config.update_pc.
    des_ifs. }
  reflexivity.
Qed.

Lemma no_mem_change_after_update:
  forall c r v,
    Ir.Config.m c = Ir.Config.m (update_reg_and_incrpc c r v).
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite <- no_mem_change_after_incrpc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

(* Lemma: inst_det_step preserves well-formedness of configuration. *)
Ltac thats_it2 := apply no_mem_change_after_update.

Lemma changes_mem_spec_det:
  forall c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HNEXT:Some (sr_success e c') = inst_det_step c),
    c.(Ir.Config.m) = c'.(Ir.Config.m).
Proof.
    intros.
    unfold inst_det_step in HNEXT. (* ibinop. *)
    rewrite <- HCUR in HNEXT.
    destruct i as [r retty bopc op1 op2 (* ibinop *)
                  |r retty ptrty opptr1 opptr2 (* ipsub *)
                  |r retty opptr opidx inb (* igep *)
                  |r retty opptr (* iload *)
                  |valty opval opptr (* istore *)
                  |(* imalloc *)
                  |opptr (* ifree *)
                  |r opval retty (* ibitcast *)
                  |r opptr retty (* iptrtoint *)
                  |r opint retty (* iinttoptr *)
                  |opval (* ievent *)
                  |r opty op1 op2 (* iicmp_eq *)
                  |r opty op1 op2 (* iicmp_ule *)
                  ] eqn:HINST; try (inversion HNEXT; fail);
      try (inversion HNOMEMCHG; fail);
      try (des_ifs; thats_it2; fail).
    + (* ievent *)
      rename HNEXT into H2. simpl in H2.
      des_op c opval opv H2. des_inv opv H2.
      inversion H2. eapply no_mem_change_after_incrpc.
Qed.

(* Theorem: if changes_mem returns false, memory isn't
   changed after inst_step. *)
Theorem changes_mem_spec:
  forall c i c' e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HSTEP:inst_step c (sr_success e c')),
    c.(Ir.Config.m) = c'.(Ir.Config.m).
Proof.
  intros.
  inversion HSTEP.
  - eapply changes_mem_spec_det. assumption.
    eassumption. assumption. eassumption.
  - (* malloc, NULL *)
    apply no_mem_change_after_update.
  - (* malloc *)
    rewrite <- HCUR in HCUR0. inversion HCUR0. rewrite H3 in HINST.
    rewrite HINST in HNOMEMCHG. inversion HNOMEMCHG.
  - (* iicmp_eq, nondet *) apply no_mem_change_after_update.
  - (* icmp_ule, nondet *) apply no_mem_change_after_update.
  - (* icmp_ule, nondet 2 *) apply no_mem_change_after_update.
Qed.

End SMALLSTEP.

End SmallStep.

End Ir.
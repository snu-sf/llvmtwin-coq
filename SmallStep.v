Require Import List.
Require Import Bool.
Require Import BinNat.
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

(* Updates register & Increments PC. *)
Definition update_reg_and_incrpc (c:Ir.Config.t) (r:Ir.reg) (v:Ir.val) :=
  incrpc (Ir.Config.update_rval c r v).


(* Helper functions *)
Definition twos_compl (n:nat) (sz:nat):nat :=
  Nat.modulo n (Nat.shiftl 2 (sz - 1)).

Definition twos_compl_add (x y:nat) (sz:nat):nat :=
  twos_compl (x + y) sz.

Definition twos_compl_sub (x y:nat) (sz:nat):nat :=
  twos_compl (x + (Nat.shiftl 2 (sz - 1)) - y) sz.

Definition to_num (b:bool): Ir.val :=
  Ir.num (if b then 1 else 0).


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

(* Convert a pointer into nat. *)
Definition p2N (p:Ir.ptrval) (m:Ir.Memory.t) (sz:nat):nat :=
  let sz := Nat.min Ir.PTRSZ sz in
  match p with
  | Ir.plog l o =>
    match Ir.log_to_phy m l o with
    | Some (Ir.pphy o' _ _) =>
      twos_compl o' sz
    | _ => twos_compl o sz (* unreachable in well-typed program *)
    end
  | Ir.pphy o _ _ =>
    twos_compl o sz
  end.

(* Raw definition of PTRSZ makes coqtop loop infinitely. *)
(* why should I do this? ... *)

Definition master_key : unit.
Proof. apply tt. Qed.

Definition locked A := let 'tt := master_key in fun x : A => x.
Definition OPAQUED_PTRSZ := locked nat Ir.PTRSZ.

(* Pointer subtraction. *)
Definition psub p1 p2 m bsz :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    if Nat.eqb l1 l2 then
      (* psub on two same block *)
      Ir.num (twos_compl (twos_compl_sub o1 o2 OPAQUED_PTRSZ) bsz)
    else
      (* psub on two different blocks *)
      Ir.poison
  (* In all other cases, returns concrete number *)
  | (Ir.pphy o1 _ _, Ir.plog _ _) =>
    Ir.num (twos_compl (twos_compl_sub o1 (p2N p2 m OPAQUED_PTRSZ) OPAQUED_PTRSZ) bsz)
  | (Ir.plog _ _, Ir.pphy o2 _ _) =>
    Ir.num (twos_compl (twos_compl_sub (p2N p1 m OPAQUED_PTRSZ) o2 OPAQUED_PTRSZ) bsz)
  | (Ir.pphy o1 _ _, Ir.pphy o2 _ _) =>
    Ir.num (twos_compl (twos_compl_sub o1 o2 OPAQUED_PTRSZ) bsz)
  end.

(* getelementptr with/without inbounds tag. *)
Definition gep (p:Ir.ptrval) (idx0:nat) (t:Ir.ty) (m:Ir.Memory.t) (inb:bool): Ir.val :=
  let idx := idx0 * (Ir.ty_bytesz t) in
  match p with
  | Ir.plog l o =>
    let o' := twos_compl_add o idx OPAQUED_PTRSZ in
    if inb then
      (* In case of inbounds: check whether input/output pointer is
         within bounds. *)
      match (Ir.Memory.get m l) with
      | Some blk =>
        if Ir.MemBlock.inbounds o blk &&
           Ir.MemBlock.inbounds o' blk then Ir.ptr (Ir.plog l o')
        else Ir.poison (* out of bounds *)
      | None => Ir.poison (* unreachable *)
      end
    else
      (* otherwise: just returns the pointer with updated offset. *)
      Ir.ptr (Ir.plog l o')
  | Ir.pphy o Is cid =>
    let o' := twos_compl_add o idx OPAQUED_PTRSZ in
    if inb then
      if Nat.ltb idx (Nat.shiftl 1 (OPAQUED_PTRSZ - 1)) then
        (* Added idx is positive. *)
        if Nat.ltb (o + idx) Ir.MEMSZ then
          (* Should not overflow Ir.MEMSZ *)
          Ir.ptr (Ir.pphy o' (o::o'::Is) cid)
        else Ir.poison
      else
        (* idx is negative: no constraint. *)
        Ir.ptr (Ir.pphy o' (o::o'::Is) cid)
    else
      (* if no inbounds tag, don't update Is. *)
      Ir.ptr (Ir.pphy o' Is cid)
  end.

(* free operation. *)
Definition free p m: option (Ir.Memory.t) :=
  match p with
  | Ir.plog l 0 => Ir.Memory.free m l
  | Ir.pphy o Is cid =>
    (* find a block which corresponds to o. *)
    match (Ir.Memory.zeroofs_block m o) with
    | None => None
    | Some (bid, mb) =>
      if Ir.deref m p 1 then (* to use Is, cid info *)
        Ir.Memory.free m bid
      else None
    end
  | _ => None
  end.

(* Returns true if `icmp eq` on two poiners will return nondeterministic
   value, false otherwise. *)
Definition icmp_eq_ptr_nondet_cond (p1 p2:Ir.ptrval) (m:Ir.Memory.t): bool :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    match (Ir.Memory.get m l1, Ir.Memory.get m l2) with
    | (Some mb1, Some mb2) =>
      (negb (Nat.eqb l1 l2)) && (* two pointers should point to diff. blocks *)
       (* o1 = n /\ o2 = 0 *)
      ((Nat.eqb o1 mb1.(Ir.MemBlock.n) && Nat.eqb o2 0) ||
       (* n < o1 *)
       (mb1.(Ir.MemBlock.n) <? o1) ||
       (* o1 = 0 /\ o2 = n *)
       (Nat.eqb o1 0 && Nat.eqb o2 mb2.(Ir.MemBlock.n)) ||
       (* n < o2 *)
       (mb2.(Ir.MemBlock.n) <? o2) ||
       (* even if offsets are inbounds, comparison result is nondeterministic
          if lifetimes are disjoint.
          Note that using <= is fine because no two blocks can have
          same birth time or end time. *)
       (match (mb1.(Ir.MemBlock.r), mb2.(Ir.MemBlock.r)) with
        | ((b1, None), (b2, None)) => false
        | ((b1, None), (b2, Some e2)) => e2 <=? b1
        | ((b1, Some e1), (b2, None)) => e1 <=? b2
        | ((b1, Some e1), (b2, Some e2)) => (e1 <=? b2) || (e2 <=? b1)
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
    Some (Nat.eqb o1 (p2N p2 m Ir.PTRSZ))
  | (_, Ir.pphy o2 Is2 cid2) =>
    Some (Nat.eqb (p2N p1 m Ir.PTRSZ) o2)
  end.

(* Returns true if `icmp ule` on two poiners will return nondeterministic
   value, false otherwise. *)
Definition icmp_ule_ptr_nondet_cond (p1 p2:Ir.ptrval) (m:Ir.Memory.t): bool :=
  match (p1, p2) with
  | (Ir.plog l1 o1, Ir.plog l2 o2) =>
    negb (Nat.eqb l1 l2) || (* they point to different blocks, or *)
    match Ir.Memory.get m l1 with
    | Some mb1 =>
      (* ~ (o1 <= n /\ o2 <= n) *)
      (negb (Nat.leb o1 (Ir.MemBlock.n mb1))) ||
      (negb (Nat.leb o2 (Ir.MemBlock.n mb1)))
    | None => false
    end
  | _ => false
  end.

(* p1 <= p2 *)
Definition icmp_ule_ptr (p1 p2:Ir.ptrval) (m:Ir.Memory.t): option bool :=
  if icmp_ule_ptr_nondet_cond p1 p2 m then None
  else Some
    match (p1, p2) with
    | (Ir.plog l1 o1, Ir.plog l2 o2) =>
      (* always l1 = l2 *)
      match (Ir.Memory.get m l1) with
      | Some mb1 => Nat.leb o1 o2
      | None => false (* unreachable *)
      end
    | (Ir.pphy o1 Is1 cid1, _) =>
      Nat.leb o1 (p2N p2 m Ir.PTRSZ)
    | (_, Ir.pphy o2 Is2 cid2) =>
      Nat.leb (p2N p1 m Ir.PTRSZ) o2
    end.

Definition binop (bopc:Ir.Inst.bopcode) (i1 i2:nat) (bsz:nat):nat :=
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
        match retty with
        | Ir.ity bsz =>
          match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
          | (Some (Ir.ptr p1), Some (Ir.ptr p2)) => psub p1 p2 (Ir.Config.m c) bsz
          | (_, _) => Ir.poison
          end
        | _ => Ir.poison
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
      | (Some Ir.poison) => Some sr_goes_wrong
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
      | (Some Ir.poison, Some v) => Some sr_goes_wrong
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
          | _ => Ir.poison (* ex: `bitcast i8* to i64' is invalid. *)
          end
        | Some (Ir.num n) =>
          match retty with
          | Ir.ity _ => Ir.num n
          | _ => Ir.poison (* ex: `bitcast i64 to i8*' is invaild. *)
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
          | Some (Ir.num n) => Ir.ptr (Ir.pphy (twos_compl n OPAQUED_PTRSZ) nil None)
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
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (Nat.eqb n1 n2))))
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
        Some (sr_success Ir.e_none (update_reg_and_incrpc c r (to_num (Nat.leb n1 n2))))
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

(* Inductive definition of small-step semantics of instruction. *)
Inductive inst_step: Ir.Config.t -> step_res -> Prop :=
(* small-step with deterministic semantics. *)
| s_det: forall c sr
      (HNEXT:Some sr = inst_det_step c), inst_step c sr

(* a case where malloc nondeterministically returns NULL.
   This is required because we really cannot expect when
   malloc will return NULL in assembly code. *)
| s_malloc_null: forall c i r szty opsz
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.imalloc r szty opsz),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.ptr Ir.NULL)))

(* a case where malloc returned oom. *)
| s_malloc_oom: forall c i r szty opsz nsz
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HSZ:Some (Ir.num nsz) = Ir.Config.get_val c opsz)
      (HNOSPACE:~exists (P:list nat),
            Ir.Memory.allocatable (Ir.Config.m c) (List.map (fun addr => (addr, nsz)) P) = true),
    inst_step c sr_oom

(* Malloc which does twin memory allocation.
   P is the list of beginning offsets.
   l is the returned block id. *)
| s_malloc: forall c i r szty opsz nsz (P:list nat) m' l contents
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.imalloc r szty opsz)
      (HSZ:Some (Ir.num nsz) = Ir.Config.get_val c opsz)
      (HSZ2:nsz > 0)
      (HC:contents = List.repeat (Ir.Byte.poison) nsz)
      (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk
                                            (Ir.heap) (begt, None) nsz
                                            (Ir.SYSALIGN) contents P))
      (HDISJ:Ir.Memory.allocatable (Ir.Config.m c)
                       (List.map (fun addr => (addr, nsz)) P) = true)
      (HNEW: (m', l) = Ir.Memory.new (Ir.Config.m c) (Ir.heap) nsz
                                     (Ir.SYSALIGN) contents P),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc
                                           (Ir.Config.update_m c m') r
                    (Ir.ptr (Ir.plog l 0))))

(* a case when icmp eq returns value nondeterminstically *)
| s_icmp_eq_nondet: forall c i r opty op1 op2 p1 p2 res
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.iicmp_eq r opty op1 op2)
      (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr p2) = Ir.Config.get_val c op2)
      (HNONDET:icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m c) = true),
    inst_step c (sr_success Ir.e_none (update_reg_and_incrpc c r (Ir.num res)))

(* a case when icmp ule returns value nondeterminstically *)
| s_icmp_ule_nondet: forall c i r opty op1 op2 p1 p2 res
      (HCUR:Some i = Ir.Config.cur_inst md c)
      (HINST:i = Ir.Inst.iicmp_ule r opty op1 op2)
      (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val c op1)
      (HOP2:Some (Ir.ptr p2) = Ir.Config.get_val c op2)
      (HNONDET:icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m c) = true),
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

Definition t_step (c:Ir.Config.t) : step_res :=
  match (Ir.Config.cur_terminator md c) with
  | Some t =>
    match t with
    | Ir.Terminator.tbr bbid =>
      (* Unconditional branch. *)
      br c bbid
         
    | Ir.Terminator.tbr_cond condop bbid_t bbid_f =>
      (* Conditional branch. *)
      let tgt :=
          match (Ir.Config.get_val c condop) with
          | Some (Ir.num cond) =>
            if Nat.eqb cond 0 then Some bbid_f
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
    end
  | _ => sr_goes_wrong
  end.

(****************************************************
             Semantics of phi node.
 ****************************************************)
Definition phi_step (bef_bbid:nat) (c:Ir.Config.t)
: option Ir.Config.t :=
  match (Ir.Config.cur_phi md c) with
  | Some p =>
    match list_find_key p.(snd) bef_bbid with
    | (_, op0)::_ =>
      match Ir.Config.get_val c op0 with
      | Some v => Some (update_reg_and_incrpc c p.(fst).(fst) v)
      | None => None
      end
    | nil => None
    end
  | _ => None
  end.

Inductive phi_bigstep: nat -> Ir.Config.t -> Ir.Config.t -> Prop :=
| pbs_one:
    forall c c' bef_bbid (HSTEP:phi_step bef_bbid c = Some c'),
    phi_bigstep bef_bbid c c'
| pbs_succ:
    forall c c' c'' bef_bbid
           (HNSTEP:phi_bigstep bef_bbid c c')
           (HSTEP:phi_step bef_bbid c' = Some c''),
    phi_bigstep bef_bbid c c''.


(****************************************************
        Semantics of a general small step.
 ****************************************************)

Definition is_pc_phi (pc0:Ir.IRFunction.pc): bool :=
  match pc0 with
  | Ir.IRFunction.pc_phi _ _ => true
  | _ => false
  end.

Inductive sstep: Ir.Config.t -> step_res -> Prop :=
| ss_inst:
    forall st sr (HISTEP:inst_step st sr),
      sstep st sr
| ss_br_goes_wrong:
    forall st t
           (HCUR:Some t = Ir.Config.cur_terminator md st)
           (HTSTEP:t_step st = sr_goes_wrong),
      sstep st sr_goes_wrong
| ss_br_success:
    (* It is assumed that phi is executed continuously
       after br is executed. This follows Vellvm's style. *)
    forall st0 fdef0 pc0 st' st'' fdef'' pc''
           (HTSTEP:t_step st0 = sr_success Ir.e_none st')
           (HCURPC:Some (fdef0, pc0) = Ir.Config.cur_fdef_pc md st0)
           (HPSTEP:phi_bigstep (pc_bbid pc0) st' st'')
           (HCURPC':Some (fdef'', pc'') = Ir.Config.cur_fdef_pc md st'')
           (HNOT_PHI_ANYMORE:is_pc_phi pc'' = false),
      sstep st0 (sr_success Ir.e_none st'').

End SMALLSTEP.

End SmallStep.

End Ir.
Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.
Require Import Omega.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Behaviors.

Module Ir.

Module SmallStepTest.

Lemma update_rval_diffval:
  forall st r v1 v2
         (HDIFF:v1 <> v2) (HNOTEMPTY:Ir.Config.s st <> []),
    Ir.Config.update_rval st r v1 <>
    Ir.Config.update_rval st r v2.
Proof.
  intros.
  unfold Ir.Config.update_rval.
  destruct (Ir.Config.s st) eqn:HS.
  - congruence.
  - destruct p. destruct p.
    intros H0.
    inv H0. congruence.
Qed.

Lemma update_reg_and_incrpc_diffval:
  forall md st r v1 v2
         (HDIFF:v1 <> v2) (HNOTEMPTY:Ir.Config.s st <> []),
    Ir.SmallStep.update_reg_and_incrpc md st r v1 <>
    Ir.SmallStep.update_reg_and_incrpc md st r v2.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.SmallStep.incrpc.
  repeat (rewrite Ir.Config.cur_fdef_pc_update_rval).
  destruct (Ir.Config.cur_fdef_pc md st) eqn:HPC.
  { destruct p. des_ifs.
    unfold Ir.Config.update_pc.
    unfold Ir.Config.update_rval.
    destruct (Ir.Config.s st) eqn:HS.
    { congruence. }
    { destruct p1. destruct p1.
      simpl. intros H0. inv H0. congruence. }
    apply update_rval_diffval; assumption.
  }
  { apply update_rval_diffval; assumption. }
Qed.




Module IcmpEq.

(****************************************************
            icmp eq 1, 2 is always false.
 ****************************************************)

Theorem icmp_eq_int_false:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 1%N))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 2%N))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0%N)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp eq 15, 15 is always true.
 ****************************************************)

Theorem icmp_eq_int_true:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15%N))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 15%N))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1%N)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp eq poison, _ is poison.
 ****************************************************)

Theorem icmp_eq_poison:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
     icmp eq ptr1, ptr2 is equivalent to o1 == o2.
 ****************************************************)

Theorem icmp_eq_ptr_sameblock:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb) 
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 == o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r
                                               (Ir.SmallStep.to_num (Nat.eqb o1 o2))).
Proof.
  intros.
  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite PeanoNat.Nat.eqb_refl in HNEXT.
    inv HNEXT.
    reflexivity.
  - (* icmp cannot be nondeteministic. *)
    rewrite HCUR in HCUR0.
    inv HCUR0.
    rewrite HOP1 in HOP0. inv HOP0.
    rewrite HOP2 in HOP3. inv HOP3.
    unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
    rewrite HBLK in HNONDET.
    rewrite PeanoNat.Nat.eqb_refl in HNONDET.
    inv HNONDET.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 and o2 are smaller than block sizes
          & two blocks are still alive,
     icmp eq ptr1, ptr2 is false.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_false1:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 < Ir.MemBlock.n mb1) (* offset is smaller than block size *)
         (HOFS2:o2 < Ir.MemBlock.n mb2)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, None)) (* the blocks are alive *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, None))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 == o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0%N)).
Proof.
  intros.
  assert (HNEQ1: o1 <> Ir.MemBlock.n mb1). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ1.
  assert (HNEQ2: o2 <> Ir.MemBlock.n mb2). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  apply PeanoNat.Nat.lt_asymm in HOFS1.
  apply PeanoNat.Nat.lt_asymm in HOFS2.
  rewrite <- PeanoNat.Nat.ltb_nlt in HOFS1, HOFS2.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HOFS2, HNEQ1, HNEQ2.
    simpl.
    rewrite orb_false_r.
    rewrite andb_false_r.
    simpl.
    rewrite HALIVE1, HALIVE2. reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = block size & 0 < o2 < block size
          & two blocks are still alive,
     icmp eq ptr1, ptr2 is false.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_false2:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 = Ir.MemBlock.n mb1) (* o1 is the block size *)
         (HOFS2:0 < o2 < Ir.MemBlock.n mb2) (* 0 < o2 < block size *)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, None)) (* the blocks are alive *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, None))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 == o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0%N)).
Proof.
  intros.
  assert (HNEQ2: o2 <> Ir.MemBlock.n mb2). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  apply <- PeanoNat.Nat.eqb_eq in HOFS1.
  destruct HOFS2 as [HOFS21 HOFS22].
  apply Nat.lt_neq in HOFS21.
  apply not_eq_sym in HOFS21.
  rewrite <- Nat.eqb_neq in HOFS21.
  apply PeanoNat.Nat.lt_asymm in HOFS22.
  rewrite <- PeanoNat.Nat.ltb_nlt in HOFS22.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HOFS21, HOFS22, HNEQ2.
    simpl.
    rewrite orb_false_r.
    rewrite andb_false_r.
    simpl.
    rewrite HALIVE1, HALIVE2.
    rewrite PeanoNat.Nat.eqb_eq in HOFS1.
    rewrite HOFS1.
    rewrite Nat.ltb_irrefl.
    reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & two blocks have disjoint life times,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)


Theorem icmp_eq_ptr_diffblock_nondet1:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2 end1 end2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, Some end1)) (* blocks' life times *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, Some end2))
         (HDISJ: end1 < beg2 \/ end2 < beg1) (* life times are disjoint. *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Config.s st <> []), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  (*assert (HNEQ1: o1 <> Ir.MemBlock.n mb1). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ1.
  assert (HNEQ2: o2 <> Ir.MemBlock.n mb2). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  apply PeanoNat.Nat.lt_asymm in HOFS1.
  apply PeanoNat.Nat.lt_asymm in HOFS2.
  rewrite <- PeanoNat.Nat.ltb_nlt in HOFS1, HOFS2.*)
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    simpl.
    rewrite HALIVE1, HALIVE2.
    inv HDISJ; rewrite <- PeanoNat.Nat.ltb_lt in H; rewrite H.
    simpl. repeat (rewrite orb_true_r). reflexivity.
    simpl. repeat (rewrite orb_true_r). reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (N.pos p))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = 0 & o2 = block size,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_nondet2:
  forall st r rty op1 op2 sr md l1 l2 o2 mb1 mb2
         (HWF:Ir.Config.wf md st) (* The input state is well-formed *)
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 0)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS2:o2 = Ir.MemBlock.n mb2) (* o2 is the block size *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Config.s st <> []), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  assert (HNEQ1: 0 <> Ir.MemBlock.n mb1).
  { (* Prove this from well-formedness of block mb1. *)
    inv HWF. inv wf_m.
    symmetry in HBLK1.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st)) in HBLK1.
    apply wf_blocks in HBLK1.
    inv HBLK1.
    unfold no_empty_range in wf_poslen.
    unfold Ir.MemBlock.P_ranges in wf_poslen.
    destruct (Ir.MemBlock.n mb1) eqn:HN.
    { induction (Ir.MemBlock.P mb1).
      { simpl in wf_twin. inv wf_twin. }
      { simpl in wf_poslen. congruence. }
    }
    { omega. }
    { reflexivity. }
  } 
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ1.
  rewrite <- PeanoNat.Nat.eqb_eq in HOFS2.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 0)
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS2, HNEQ1.
    simpl.
    reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (N.pos p))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = block size & o2 = 0,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_nondet3:
  forall st r rty op1 op2 sr md l1 l2 o1 mb1 mb2
         (HWF:Ir.Config.wf md st) (* The input state is well-formed *)
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 0)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 = Ir.MemBlock.n mb1) (* o2 is the block size *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Config.s st <> []), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  assert (HNEQ2: 0 <> Ir.MemBlock.n mb2).
  { (* Prove this from well-formedness of block mb1. *)
    inv HWF. inv wf_m.
    symmetry in HBLK2.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st)) in HBLK2.
    apply wf_blocks in HBLK2.
    inv HBLK2.
    unfold no_empty_range in wf_poslen.
    unfold Ir.MemBlock.P_ranges in wf_poslen.
    destruct (Ir.MemBlock.n mb2) eqn:HN.
    { induction (Ir.MemBlock.P mb2).
      { simpl in wf_twin. inv wf_twin. }
      { simpl in wf_poslen. congruence. }
    }
    { omega. }
    { reflexivity. }
  }
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  rewrite <- PeanoNat.Nat.eqb_eq in HOFS1.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1)
                (Ir.plog l2 0) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HNEQ2.
    simpl.
    reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0%N))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (N.pos p))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

End IcmpEq.



Module IcmpUle.

(****************************************************
            icmp ule 1, 2 is always true.
 ****************************************************)

Theorem icmp_ule_int_true1:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 1%N))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 2%N))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1%N)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule 15, 15 is always true.
 ****************************************************)

Theorem icmp_ule_int_true2:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15%N))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 15%N))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1%N)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule 15, 14 is always false.
 ****************************************************)

Theorem icmp_ule_int_false:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15%N))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 14%N))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0%N)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule poison, _ is always poison.
 ****************************************************)

Theorem icmp_ule_poison:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
       & o1 <= block size & o2 <= block size,
     icmp ule ptr1, ptr2 is equivalent to o1 <= o2.
 ****************************************************)

Theorem icmp_ule_ptr_sameblock_det:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb)
         (HOFS1:o1 <= Ir.MemBlock.n mb)
         (HOFS2:o2 <= Ir.MemBlock.n mb)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 == o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r
                                               (Ir.SmallStep.to_num (Nat.leb o1 o2))).
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l o1)
                (Ir.plog l o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite HBLK.
    rewrite <- PeanoNat.Nat.leb_le in HOFS1, HOFS2.
    rewrite HOFS1. rewrite HOFS2. reflexivity. }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    rewrite HBLK in HNEXT.
    inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
       & (block size < o1 \/ block size < o2),
  icmp ule ptr1, ptr2 yields nondeterministic value.
 ****************************************************)

Theorem icmp_ule_ptr_sameblock_nondet:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb)
         (HOFS:Ir.MemBlock.n mb < o1 \/ Ir.MemBlock.n mb < o2)
         (HSTACKNOTEMPTY:Ir.Config.s st <> []) (* there exists a register file *)
         (HINST:Ir.SmallStep.inst_step md st sr),
    exists sr',
      Ir.SmallStep.inst_step md st sr' /\
      sr' <> sr.
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l o1)
                (Ir.plog l o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite HBLK.
    repeat (rewrite Nat.lt_nge in HOFS).
    repeat (rewrite <- Nat.leb_nle in HOFS).
    destruct HOFS.
    { rewrite H. reflexivity. }
    { rewrite H. simpl. rewrite orb_true_r. reflexivity. }
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    inv HNEXT.
  - rewrite HCUR in HCUR0.
    inv HCUR0.
    destruct res.
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
        { apply update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num (N.pos p)))).
        { apply update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }   
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2),
  icmp ule ptr1, ptr2 yields nondeterministic value.
 ****************************************************)

Theorem icmp_ule_ptr_diffblock_nondet:
  forall st r rty op1 op2 sr md l1 l2 o1 o2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HSTACKNOTEMPTY:Ir.Config.s st <> []) (* there exists a register file *)
         (HINST:Ir.SmallStep.inst_step md st sr),
    exists sr',
      Ir.SmallStep.inst_step md st sr' /\
      sr' <> sr.
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l1 o1)
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.
    rewrite HDIFFBLK. reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    inv HNEXT.
  - rewrite HCUR in HCUR0.
    inv HCUR0.
    destruct res.
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
        { apply update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num (N.pos p)))).
        { apply update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }   
Qed.


End IcmpUle.

End SmallStepTest.

End Ir.

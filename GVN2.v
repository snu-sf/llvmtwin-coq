Require Import Bool.
Require Import Sorting.Permutation.
Require Import Omega.
Require Import sflib.
Require Import Lia.

Require Import Common.
Require Import Value.
Require Import Lang.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Refinement.
Require Import SmallStepRefinement.
Require Import Reordering.

Module Ir.

Module GVN2.


(* 2nd condition of replacing p with q:
   If p and q are both logical pointers, and
   either they point to the same block or
   they are both dereferenceable. *)
Definition eqprop_valid (m:Ir.Memory.t) (p q:Ir.val) :=
  exists l1 o1 l2 o2,
    p = Ir.ptr (Ir.plog l1 o1) /\ q = Ir.ptr (Ir.plog l2 o2) /\
    (l1 = l2 \/ (* they are logical ptrs on the same block, or *)
       (* they are dereferenceable (with minimal access size) *)
      (Ir.deref m (Ir.plog l1 o1) 1 = true /\
       Ir.deref m (Ir.plog l2 o2) 1 = true)).


(*********************************************************
 Critical property of eqprop_valid:
  If eqprop_valid p q holds, and `icmp eq p, q` evaluates
    to true, then p and q are exactly the same pointer!
 *********************************************************)


Theorem eqprop_valid_after_icmpeq_true:
  forall md st st' r ptrty op1 op2 v1 v2 e
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iicmp_eq r ptrty op1 op2) = Ir.Config.cur_inst md st)
    (HOP1:Some v1 = Ir.Config.get_val st op1)
    (HOP2:Some v2 = Ir.Config.get_val st op2)
    (* eqprop_valid holds *)
    (HEQPROP:eqprop_valid (Ir.Config.m st) v1 v2)
    (* have a small step *)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st'))
    (* p1 == p2 is true *)
    (HTRUE:Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r)),

    v1 = v2.
Proof.
  intros.
  assert (HS:Ir.Config.s st <> []).
  {
    unfold Ir.Config.cur_inst in HINST.
    unfold Ir.Config.cur_fdef_pc in HINST.
    des_ifs.
  }

  inv HSTEP.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      rewrite <- HOP1, <- HOP2 in HNEXT.
      inv HEQPROP.
      inv H. inv H0. inv H. inv H0. inv H1.
      des_ifs.
      rewrite Ir.Reordering.get_val_update_reg_and_incrpc in HTRUE.
      unfold Ir.Config.get_val in HTRUE.
      rewrite Ir.Config.get_rval_update_rval_id in HTRUE; try assumption.
      unfold Ir.SmallStep.icmp_eq_ptr in Heq.
      destruct H0.
      { (* same block id *)
        subst x.
        rewrite Nat.eqb_refl in Heq. inv Heq. inv HTRUE.
        des_ifs. rewrite Nat.eqb_eq in Heq. congruence.
      }
      { destruct H.
        destruct (x =? x1) eqn:HEQ.
        { rewrite Nat.eqb_eq in HEQ. subst x.
          inv Heq. inv HTRUE. des_ifs. rewrite Nat.eqb_eq in Heq.
          subst x0. reflexivity. }
        { (* okay, when the blocks are different. *)
          unfold Ir.deref in *.
          des_ifs. }
      }
    }
    { rewrite <- HINST in HCUR. inv HCUR.
      rewrite Ir.Reordering.get_val_update_reg_and_incrpc in HTRUE.
      unfold Ir.Config.get_val in HTRUE.
      rewrite Ir.Config.get_rval_update_rval_id in HTRUE; try assumption.
      inv HTRUE.
      inv HEQPROP.
      inv H.  inv H0. inv H. inv H0. inv H1.
      rewrite <- HOP1 in HOP0. inv HOP0.
      rewrite <- HOP2 in HOP3. inv HOP3.
      (* let's get blkid difference from icmp eq nondet cond. *)
      assert (HDIFFBLK:x =? x1 = false).
      {
        unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
        des_ifs;
        destruct (x =? x1) eqn:TT; try simpl in HNONDET; try congruence.
      }
      rewrite Nat.eqb_neq in HDIFFBLK.
      destruct H0; try congruence.
      inv H.
      unfold Ir.deref in *.
      des_ifs.
      destruct p0. destruct p0. destruct p. destruct p.
      (* singleton-ize get_derefs. *)
      (* preparing Memory.get s.. *)
      inv HWF.
      symmetry in HOP1. apply wf_no_bogus_ptr in HOP1. inv HOP1.
      symmetry in HOP2. apply wf_no_bogus_ptr in HOP2. inv HOP2.
      (* Okay, start! op1 *)
      dup Heq0.
      eapply Ir.get_deref_log in Heq1; try eassumption.
      destruct Heq1; try congruence. inv H3.
      (* okay, next op2. *)
      dup Heq.
      eapply Ir.get_deref_log in Heq1; try eassumption.
      destruct Heq1; try congruence. inv H3.
      (* okay, time to get inbounds conditions. *)
      eapply Ir.get_deref_inv in Heq0.
      eapply Ir.get_deref_inv in Heq.
      repeat (rewrite andb_true_iff in *).
      destruct Heq0. destruct H3. destruct Heq. destruct H6.
      unfold Ir.MemBlock.inbounds in H5, H4, H8, H7.
      (* Now, go toward contradiction. *)
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
      rewrite H, H2 in HNONDET.
      rewrite <- Nat.eqb_neq in HDIFFBLK. rewrite HDIFFBLK in HNONDET.
      unfold Ir.MemBlock.alive in *.
      destruct (Ir.MemBlock.r x3) as [beg1 end1].
      simpl in H3. destruct end1; try congruence.
      destruct (Ir.MemBlock.r x4) as [beg2 end2].
      simpl in H6. destruct end2; try congruence.
      rewrite orb_false_r in HNONDET.
      simpl in HNONDET.
      assert (Ir.MemBlock.n x3 <? x0 = false).
      { rewrite Nat.ltb_ge. rewrite  Nat.leb_le in H5. omega. }
      rewrite H9 in HNONDET.
      assert (Ir.MemBlock.n x4 <? x2 = false).
      { rewrite Nat.ltb_ge. rewrite  Nat.leb_le in H7. omega. }
      rewrite H10 in HNONDET.
      assert (x0 =? Ir.MemBlock.n x3 = false).
      { rewrite Nat.eqb_neq. rewrite Nat.leb_le in H4. omega. }
      rewrite H11 in HNONDET.
      assert (x2 =? Ir.MemBlock.n x4 = false).
      { rewrite Nat.eqb_neq. rewrite Nat.leb_le in H7. omega. }
      rewrite H12 in HNONDET.
      rewrite andb_false_r in HNONDET.
      simpl in HNONDET. congruence.

      omega.
      assumption.
      assumption.
      omega.
      assumption.
      assumption.
    }
  }
  { (* terminator! *)
    apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    unfold Ir.SmallStep.t_step in HTSTEP.
    rewrite <- HINST in HTSTEP. congruence.
  }
Qed.


(*********************************************************
    Okay, from theorem `eqprop_valid_after_icmpeq_true`,
    we can say that two pointers have same value after
    `p == q` check.
    It is trivial to have same execution when same value
    is given, hence not proved.
 *********************************************************)

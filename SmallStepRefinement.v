Require Import Bool.
Require Import Sorting.Permutation.
Require Import Omega.
Require Import sflib.

Require Import Common.
Require Import Value.
Require Import Lang.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Refinement.

Module Ir.

Module Refinement.

Import Refinement.
Import Ir.Refinement.

Lemma eq_incrpc:
  forall md1 md2 st i1 i2
      (HINST1: Some i1 = Ir.Config.cur_inst md1 st)
      (HINST2: Some i2 = Ir.Config.cur_inst md2 st),
    Ir.Config.eq (Ir.SmallStep.incrpc md1 st) (Ir.SmallStep.incrpc md2 st).
Proof.
  intros.
  unfold Ir.Config.cur_inst in HINST1.
  unfold Ir.Config.cur_inst in HINST2.
  split.
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      repeat (rewrite Ir.Config.m_update_pc);
      unfold Ir.Config.update_rval; des_ifs.
  }
  split.
  { unfold Ir.Config.cur_fdef_pc in HINST1.
    unfold Ir.Config.cur_fdef_pc in HINST2.
    des_ifs.
    unfold Ir.IRFunction.get_inst in HINST1.
    unfold Ir.IRFunction.get_inst in HINST2.
    destruct p1; try congruence.
    des_ifs.
    unfold Ir.SmallStep.incrpc.
    unfold Ir.Config.cur_fdef_pc.
    rewrite Heq0.
    rewrite Heq1.
    rewrite Heq2.
    rewrite Heq3.
    unfold Ir.IRFunction.next_trivial_pc.
    rewrite Heq5.
    rewrite Heq.
    rewrite Heq6.
    rewrite Heq4.
    apply Ir.Stack.eq_refl.
  }
  split.
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; des_ifs.
  }
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; des_ifs.
  }
Qed.

Lemma inst_next_pc_notnone:
  forall md st fdef pc i1
         (HPC:Ir.Config.cur_fdef_pc md st = Some (fdef, pc))
         (HINST:Some i1 = Ir.IRFunction.get_inst pc fdef),
    Ir.IRFunction.next_trivial_pc pc fdef <> None.
Proof.
  intros.
  unfold Ir.IRFunction.next_trivial_pc.
  unfold Ir.IRFunction.get_inst in HINST.
  des_ifs.
Qed.

Lemma cid_to_f_update_pc:
  forall st p,
    Ir.Config.cid_to_f (Ir.Config.update_pc st p) =
    Ir.Config.cid_to_f st.
Proof.
  intros.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Lemma cid_fresh_update_pc:
  forall st p,
    Ir.Config.cid_fresh (Ir.Config.update_pc st p) =
    Ir.Config.cid_fresh st.
Proof.
  intros.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Theorem refines_incrpc:
  forall md1 md2 st1 st2 i1 i2
      (HINST1: Some i1 = Ir.Config.cur_inst md1 st1)
      (HINST2: Some i2 = Ir.Config.cur_inst md2 st2)
      (HREFINES: refines_state st1 st2),
    refines_state (Ir.SmallStep.incrpc md1 st1) (Ir.SmallStep.incrpc md2 st2).
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  inv HREFINES.
  split.
  { simpl.
    des_ifs; repeat (rewrite Ir.Config.m_update_pc); assumption.
  }
  inv H0. split.
  { unfold Ir.Config.cur_inst in HINST1, HINST2.
    des_ifs.
    { unfold Ir.Config.cur_fdef_pc in Heq1, Heq.
      unfold Ir.Config.update_pc.
      des_ifs.
      simpl. 
      inv H1.
      simpl in H5. inv H5. inv H1.
      constructor.
      simpl. split. congruence. split.
      { unfold Ir.IRFunction.next_trivial_pc in Heq0, Heq2.
        des_ifs. }
      assumption.
      assumption.
    }
    { eapply inst_next_pc_notnone in HINST2;
        try eassumption.
      congruence.
    }
    { eapply inst_next_pc_notnone in HINST1;
        try eassumption.
      congruence.
    }
  }
  inv H2. split.
  { des_ifs; repeat (rewrite cid_to_f_update_pc); congruence. }
  { des_ifs; repeat (rewrite cid_fresh_update_pc); congruence. }
Qed.  


Lemma eq_update_reg_and_incrpc2:
  forall md1 md2 st r v i1 i2
      (HINST1: Some i1 = Ir.Config.cur_inst md1 st)
      (HINST2: Some i2 = Ir.Config.cur_inst md2 st),
    Ir.Config.eq
      (Ir.SmallStep.update_reg_and_incrpc md1 st r v)
      (Ir.SmallStep.update_reg_and_incrpc md2 st r v).
Proof.
  intros.
  unfold Ir.Config.cur_inst in HINST1.
  unfold Ir.Config.cur_inst in HINST2.
  split.
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      repeat (rewrite Ir.Config.m_update_pc);
      unfold Ir.Config.update_rval; des_ifs.
  }
  split.
  { unfold Ir.Config.cur_fdef_pc in HINST1.
    unfold Ir.Config.cur_fdef_pc in HINST2.
    des_ifs.
    unfold Ir.IRFunction.get_inst in HINST1.
    unfold Ir.IRFunction.get_inst in HINST2.
    destruct p1; try congruence.
    des_ifs.
    unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    rewrite Ir.Config.cur_fdef_pc_update_rval.
    rewrite Ir.Config.cur_fdef_pc_update_rval.
    unfold Ir.Config.cur_fdef_pc.
    rewrite Heq0.
    rewrite Heq1.
    rewrite Heq2.
    rewrite Heq3.
    unfold Ir.IRFunction.next_trivial_pc.
    rewrite Heq5.
    rewrite Heq.
    rewrite Heq6.
    rewrite Heq4.
    apply Ir.Stack.eq_refl.
  }
  split.
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; unfold Ir.Config.update_rval;
      des_ifs.
  }
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; unfold Ir.Config.update_rval;
      des_ifs.
  }
Qed.


End Refinement.

End Ir.
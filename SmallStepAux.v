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
Require Import SmallStep.

Import SmallStep.
Import Ir.
Import Ir.SmallStep.

Module Ir.

Module SmallStep.

(****************************************************
Auxiliary Lemmas about PTRSZ,MEMSZ,two's complement,etc
 ****************************************************)

Lemma OPAQUED_PTRSZ_PTRSZ:
  Ir.SmallStep.OPAQUED_PTRSZ = Ir.PTRSZ.
Proof.
  unfold Ir.SmallStep.OPAQUED_PTRSZ.
  unfold Ir.SmallStep.locked.
  des_ifs.
Qed.

Lemma PTRSZ_MEMSZ:
  Nat.shiftl 2 (Ir.PTRSZ - 1) = Ir.MEMSZ.
Proof. unfold Ir.MEMSZ; rewrite Ir.PTRSZ_def. reflexivity. Qed.

Lemma PTRSZ_MEMSZ2:
  Nat.double (Nat.shiftl 1 (Ir.PTRSZ - 1)) = Ir.MEMSZ.
Proof. unfold Ir.MEMSZ; rewrite Ir.PTRSZ_def. reflexivity. Qed.

Lemma twos_compl_add_lt:
  forall a b,
    twos_compl_add a b Ir.PTRSZ < Ir.MEMSZ.
Proof.
  unfold twos_compl_add. unfold twos_compl.
  intros. rewrite PTRSZ_MEMSZ. apply Nat.mod_upper_bound.
  pose Ir.MEMSZ_pos. omega.
Qed.

Lemma twos_compl_lt:
  forall a,
    twos_compl a Ir.PTRSZ < Ir.MEMSZ.
Proof.
  unfold twos_compl.
  intros. rewrite PTRSZ_MEMSZ. apply Nat.mod_upper_bound.
  pose Ir.MEMSZ_pos. omega.
Qed.



(****************************************************
        Auxiliary Lemmas about SmallStep.
 ****************************************************)

Lemma get_val_incrpc:
  forall md st r,
    Ir.Config.get_val (incrpc md st) r = Ir.Config.get_val st r.
Proof.
  intros.
  unfold Ir.Config.get_val.
  unfold incrpc.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.get_rval.
  unfold Ir.Config.update_pc.
  simpl.
  des_ifs; try congruence.
  simpl in Heq. inv Heq. try congruence.
Qed.

Lemma incrpc_update_rval:
  forall md st r v,
    incrpc md (Ir.Config.update_rval st r v) =
    Ir.Config.update_rval (incrpc md st) r v.
Proof.
  intros.
  unfold incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  des_ifs.
  unfold Ir.Config.update_rval.
  destruct (Ir.Config.s st) eqn:Hs.
  - unfold Ir.Config.update_pc at 2. repeat (rewrite Hs). reflexivity.
  - unfold Ir.Config.update_pc at 2. repeat (rewrite Hs).
    destruct p1 eqn:Hp1.
    destruct p2 eqn:Hp2.
    simpl. unfold Ir.Config.update_pc at 1. simpl.
    unfold Ir.Config.update_pc. repeat (rewrite Hs). simpl.
    reflexivity.
Qed.

Lemma cur_inst_update_reg_and_incrpc:
  forall md st r v,
    Ir.Config.cur_inst md (update_reg_and_incrpc md st r v) =
    Ir.Config.cur_inst md (incrpc md st).
Proof.
  intros.
  unfold Ir.Config.cur_inst.
  unfold update_reg_and_incrpc.
  rewrite incrpc_update_rval.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  reflexivity.
Qed.

Lemma m_update_reg_and_incrpc:
  forall md st r v,
    Ir.Config.m (update_reg_and_incrpc md st r v) =
    Ir.Config.m st.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  unfold incrpc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

Lemma m_incrpc:
  forall md st,
    Ir.Config.m (incrpc md st) =
    Ir.Config.m st.
Proof.
  intros.
  unfold incrpc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

Lemma incrpc_update_reg_and_incrpc:
  forall md st r v,
    incrpc md (update_reg_and_incrpc md st r v) =
    update_reg_and_incrpc md (incrpc md st) r v.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite incrpc_update_rval.
  reflexivity.
Qed.

Lemma get_val_const_update_reg_and_incrpc:
  forall md st r v c,
    Ir.Config.get_val (update_reg_and_incrpc md st r v) (Ir.opconst c) =
    Ir.Config.get_val st (Ir.opconst c).
Proof.
  intros.
  unfold Ir.Config.get_val.
  des_ifs.
Qed.

Lemma get_val_independent:
  forall md r1 r2 (HNEQ:r1 <> r2) st v,
    Ir.Config.get_val (update_reg_and_incrpc md st r2 v) (Ir.opreg r1) =
    Ir.Config.get_val st (Ir.opreg r1).
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite get_val_incrpc.
  unfold Ir.Config.get_val.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.get_rval.
  des_ifs.
  congruence. simpl in Heq. inv Heq.
  unfold Ir.Regfile.update. unfold Ir.Regfile.get.
  simpl. apply not_eq_sym in HNEQ. rewrite <- PeanoNat.Nat.eqb_neq in HNEQ.
  rewrite HNEQ. reflexivity.
Qed.

Lemma get_val_independent2:
  forall md r2 opv st v
         (HNEQ:opv <> Ir.opreg r2),
    Ir.Config.get_val (update_reg_and_incrpc md st r2 v) opv =
    Ir.Config.get_val st opv.
Proof.
  intros.
  destruct opv.
  - rewrite get_val_const_update_reg_and_incrpc. reflexivity.
  - assert (r <> r2).
    { intros H2. rewrite H2 in HNEQ. apply HNEQ. reflexivity. }
    apply get_val_independent. assumption.
Qed.

Lemma config_eq_wopc_incrpc:
  forall md st1 st2
         (HEQ:Ir.Config.eq_wopc st1 st2),
    Ir.Config.eq_wopc
      (incrpc md st1) st2.
Proof.
  intros.
  assert (HEQ_copy := HEQ).
  unfold Ir.Config.eq_wopc in HEQ.
  desH HEQ.
  split.
  - rewrite m_incrpc.
    assumption.
  - split.
    + unfold incrpc.
      des_ifs; unfold Ir.Config.update_pc.
      des_ifs.
      * inv HEQ0. rewrite Heq1. constructor.
      * inv HEQ0. simpl. simpl in H2. desH H2.
        destruct y. destruct p2.
        unfold Ir.Stack.eq_wopc. constructor.
        simpl in *. split. assumption. assumption.
        assumption.
    + split.
      * unfold incrpc.
        des_ifs.
        unfold Ir.Config.update_pc.
        des_ifs.
      * unfold incrpc.
        des_ifs.
        unfold Ir.Config.update_pc.
        des_ifs.
Qed.

Lemma incrpc_update_m:
  forall md st m,
         incrpc md (Ir.Config.update_m st m) =
         Ir.Config.update_m (incrpc md st) m.
Proof.
  intros.
  unfold incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_m.
  des_ifs. rewrite Ir.Config.update_pc_update_m. reflexivity.
Qed.

Lemma update_reg_and_incrpc_update_m:
  forall md st m r v,
    update_reg_and_incrpc md (Ir.Config.update_m st m) r v=
    Ir.Config.update_m (update_reg_and_incrpc md st r v) m.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite Ir.Config.update_rval_update_m.
  rewrite incrpc_update_m. reflexivity.
Qed.

Lemma cid_to_f_update_reg_and_incrpc:
  forall md (st:Ir.Config.t) r v,
    Ir.Config.cid_to_f (update_reg_and_incrpc md st r v) =
    Ir.Config.cid_to_f st.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  unfold incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Lemma cid_fresh_update_reg_and_incrpc:
  forall md (st:Ir.Config.t) r v,
    Ir.Config.cid_fresh (update_reg_and_incrpc md st r v) =
    Ir.Config.cid_fresh st.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  unfold incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Lemma stack_eq_wopc_incrpc:
  forall st1 st2  (md1 md2:Ir.IRModule.t)
         (HEQ:Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s st2)),
    Ir.Stack.eq_wopc (Ir.Config.s (@incrpc md1 st1))
                  (Ir.Config.s (@incrpc md2 st2)).
Proof.
  intros.
  unfold incrpc.
  des_ifs.
  - apply Ir.Config.stack_eq_wopc_update_pc1.
    apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc1. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc1. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
Qed.


Lemma eq_wopc_update_reg_and_incrpc_update_m_reorder:
  forall md1 md2 st r v m,
    Ir.Config.eq_wopc
      (update_reg_and_incrpc md1 (Ir.Config.update_m st m) r v)
      (Ir.Config.update_m (update_reg_and_incrpc md2 st r v) m).
Proof.
  intros.
  split.
  - rewrite m_update_reg_and_incrpc.
    unfold Ir.Config.update_m. reflexivity.
  - split.
    {
      rewrite update_reg_and_incrpc_update_m.
      unfold Ir.Config.update_m. simpl.
      unfold update_reg_and_incrpc.
      apply stack_eq_wopc_incrpc. apply Ir.Stack.eq_wopc_refl.
    }
    { split. rewrite update_reg_and_incrpc_update_m. unfold Ir.Config.update_m. simpl.
      repeat (rewrite cid_to_f_update_reg_and_incrpc). reflexivity.
      rewrite update_reg_and_incrpc_update_m. unfold Ir.Config.update_m. simpl.
      repeat (rewrite cid_fresh_update_reg_and_incrpc). reflexivity. }
Qed.

Lemma eq_wopc_update_reg_and_incrpc_reorder:
  forall md1 md2 st r1 r2 v1 v2
         (HNEQ:r2 <> r1),
    Ir.Config.eq_wopc
      (update_reg_and_incrpc md1
        (update_reg_and_incrpc md1 st r1 v1) r2 v2)
      (update_reg_and_incrpc md2
        (update_reg_and_incrpc md2 st r2 v2) r1 v1).
Proof.
  intros.
  unfold update_reg_and_incrpc.
  apply config_eq_wopc_incrpc.
  rewrite <- incrpc_update_rval.
  rewrite <- incrpc_update_rval.
  apply config_eq_wopc_incrpc.
  apply Ir.Config.eq_wopc_symm.
  apply config_eq_wopc_incrpc.
  apply config_eq_wopc_incrpc.
  split.
  { unfold Ir.Config.update_rval. des_ifs. }
  split.
  { unfold Ir.Config.update_rval. des_ifs; simpl in *.
    - rewrite Heq1. constructor.
    - inv Heq. inv Heq1.
      unfold Ir.Regfile.update.
      unfold Ir.Stack.eq.
      constructor.
      + simpl. split. reflexivity.
        unfold Ir.Regfile.eq.
        intros.
        unfold Ir.Regfile.get.
        simpl.
        des_ifs; try congruence.
        * rewrite PeanoNat.Nat.eqb_eq in *.
          congruence.
      + clear Heq0.
        induction t3. constructor. constructor.
        split. reflexivity. apply Ir.Regfile.eq_refl.
        apply IHt3.
  }
  split.
  { unfold Ir.Config.update_rval.
    unfold Ir.Config.cid_to_f. des_ifs.
  }
  { unfold Ir.Config.update_rval.
    unfold Ir.Config.cid_fresh. des_ifs.
  }
Qed.

Lemma update_pc_incrpc:
  forall md st p,
    Ir.Config.update_pc (incrpc md st) p =
    Ir.Config.update_pc st p.
Proof.
  intros.
  unfold incrpc.  
  unfold Ir.Config.update_pc.
  des_ifs; simpl in *.
  - rewrite Heq2 in Heq. congruence.
  - inv Heq.  reflexivity.
Qed.

Lemma cur_inst_incrpc_update_m:
  forall md m st,
    Ir.Config.cur_inst md (incrpc md (Ir.Config.update_m st m)) =
    Ir.Config.cur_inst md (incrpc md st).
Proof.
  intros.
  rewrite incrpc_update_m.
  rewrite Ir.Config.cur_inst_update_m.
  reflexivity.
Qed.

Lemma get_val_update_reg_and_incrpc:
  forall md st r v o,
    Ir.Config.get_val (update_reg_and_incrpc md st r v) o =
    Ir.Config.get_val (Ir.Config.update_rval st r v) o.
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite get_val_incrpc. reflexivity.
Qed.

Lemma get_val_update_reg_and_incrpc_samereg:
  forall md st r v
         (HSTACK:Ir.Config.s st <> nil), (* stack is not empty. *)
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r v)
                      (Ir.opreg r) =
    Some v.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.Config.get_val.
  unfold Ir.Config.get_rval.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.get_funid.
  unfold Ir.Config.update_rval.
  destruct (Ir.Config.s st); try congruence.
  destruct p. destruct p.
  simpl.
  destruct (list_find_key (Ir.Config.cid_to_f st) c).
  { simpl. apply Ir.Regfile.get_update. }
  { simpl.
    des_ifs.
    - simpl in Heq. inv Heq. apply Ir.Regfile.get_update.
    - simpl in Heq. inv Heq. apply Ir.Regfile.get_update.
    - simpl in Heq. inv Heq. apply Ir.Regfile.get_update.
  }
Qed.  

Lemma m_incrpc_update_m:
  forall md' st t,
    Ir.Config.m (incrpc md' (Ir.Config.update_m st t)) = t.
Proof.
  intros.
  rewrite incrpc_update_m.
  reflexivity.
Qed.

Lemma get_val_incrpc_update_m:
  forall md' st op11 t,
    Ir.Config.get_val (incrpc md' (Ir.Config.update_m st t)) op11 =
    Ir.Config.get_val st op11.
Proof.
  intros.
  rewrite incrpc_update_m.
  rewrite Ir.Config.get_val_update_m.
  rewrite get_val_incrpc.
  reflexivity.
Qed.

Lemma eq_wom_update_reg_and_incrpc:
  forall st1 st2 md r v (HEQ:Ir.Config.eq_wom st1 st2),
    Ir.Config.eq_wom
      (Ir.SmallStep.update_reg_and_incrpc md st1 r v)
      (Ir.SmallStep.update_reg_and_incrpc md st2 r v).
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  destruct st1.
  destruct st2.
  split.
  { unfold Ir.Config.update_rval.
    simpl.
    destruct s; destruct s0.
    { unfold Ir.SmallStep.incrpc. simpl. constructor. }
    { inv HEQ. simpl in H. inv H. }
    { inv HEQ. simpl in H. inv H. }
    { inv HEQ. simpl in H. inv H. destruct H4.
      destruct p. destruct p0. simpl in H.
      inv H. destruct H1. simpl in H.
      destruct p. destruct p0. inv H. simpl in H1. simpl in *. subst p.
      unfold Ir.SmallStep.incrpc.
      unfold Ir.Config.cur_fdef_pc. unfold Ir.Config.get_funid.
      destruct H0. subst.
      unfold Ir.Config.update_pc.
      simpl. des_ifs; simpl.
      { constructor. simpl.
        split. reflexivity.
        split. reflexivity.
        apply Ir.Regfile.update_eq. assumption.
        assumption.
      }
      { constructor. simpl.
        split. reflexivity.
        split. reflexivity.
        apply Ir.Regfile.update_eq. assumption.
        assumption.
      }
      { constructor. simpl.
        split. reflexivity.
        split. reflexivity.
        apply Ir.Regfile.update_eq. assumption.
        assumption.
      }
      { constructor. simpl.
        split. reflexivity.
        split. reflexivity.
        apply Ir.Regfile.update_eq. assumption.
        assumption.
      }
    }
  }
  split.
  { unfold Ir.Config.update_rval.
    unfold Ir.SmallStep.incrpc.
    simpl.
    inv HEQ. inv H0. simpl in H1. subst cid_to_f.
    des_ifs.
  }
  { unfold Ir.Config.update_rval.
    unfold Ir.SmallStep.incrpc.
    simpl.
    inv HEQ. inv H0. simpl in H2. subst cid_fresh.
    des_ifs.
  }
Qed.

End SmallStep.

End Ir.
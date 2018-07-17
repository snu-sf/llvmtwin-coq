Require Import Bool.
Require Import BinNat.
Require Import sflib.
Require Import Omega.
Require Import Permutation.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Behaviors.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Reordering.


Module Ir.

(* Definition of 'twin' states.*)
Definition twin_state (st1 st2:Ir.Config.t) (blkid:Ir.blockid):Prop :=
  Ir.Config.eq_wom st1 st2 /\
  Ir.Memory.mt (Ir.Config.m st1) = Ir.Memory.mt (Ir.Config.m st2) /\
  Ir.Memory.calltimes (Ir.Config.m st1) = Ir.Memory.calltimes (Ir.Config.m st2) /\
  Ir.Memory.fresh_bid (Ir.Config.m st1) = Ir.Memory.fresh_bid (Ir.Config.m st2) /\
  forall bid',
    (forall (HMATCH:bid' = blkid),
        exists mb1 mb2,
          Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid /\
          Some mb2 = Ir.Memory.get (Ir.Config.m st2) blkid /\
          (Ir.MemBlock.bt mb1) = (Ir.MemBlock.bt mb2) /\
          (Ir.MemBlock.r mb1) = (Ir.MemBlock.r mb2) /\
          (Ir.MemBlock.n mb1) = (Ir.MemBlock.n mb2) /\
          (Ir.MemBlock.a mb1) = (Ir.MemBlock.a mb2) /\
          (Ir.MemBlock.c mb1) = (Ir.MemBlock.c mb2) /\
          Permutation (Ir.MemBlock.P mb1) (Ir.MemBlock.P mb2) /\
          List.hd 0 (Ir.MemBlock.P mb1) <> List.hd 0 (Ir.MemBlock.P mb2))
    /\
    (forall (HMATCH:bid' <> blkid),
        Ir.Memory.get (Ir.Config.m st1) bid' =
        Ir.Memory.get (Ir.Config.m st2) bid').

(* Given two small step results (e.g. success/goes wrong/oom/program end),
   they are twin if it satisfies one of the followings. *)
Inductive twin_sresult:
Ir.SmallStep.step_res -> Ir.SmallStep.step_res -> Ir.blockid -> Prop :=
  | ts_success:
      forall st1 st2 (sr1 sr2:Ir.SmallStep.step_res) (e1 e2:Ir.event) blkid
             (HSR1:sr1 = Ir.SmallStep.sr_success e1 st1)
             (HSR2:sr2 = Ir.SmallStep.sr_success e2 st2)
             (HTWIN:twin_state st1 st2 blkid),
        twin_sresult sr1 sr2 blkid
  | ts_goes_wrong:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_goes_wrong)
             (HSR1:sr2 = Ir.SmallStep.sr_goes_wrong),
        twin_sresult sr1 sr2 blkid
  | ts_oom:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_oom)
             (HSR1:sr2 = Ir.SmallStep.sr_oom),
        twin_sresult sr1 sr2 blkid
  | ts_prog_finish:
      forall sr1 sr2 blkid v
             (HSR1:sr1 = Ir.SmallStep.sr_prog_finish v)
             (HSR1:sr2 = Ir.SmallStep.sr_prog_finish v),
        twin_sresult sr1 sr2 blkid.

(* A memory block blkid is observed at state st if.. *)
Inductive observes_block (md:Ir.IRModule.t) (st:Ir.Config.t) (blkid:Ir.blockid):Prop :=
  | ob_by_ptrtoint:
      forall r op1 retty o
             (HINST:Some (Ir.Inst.iptrtoint r op1 retty) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1),
        observes_block md st blkid
  | ob_by_iicmpeq_l:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_eq r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_iicmpeq_r:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_eq r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid
  | ob_by_iicmpule_l:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_ule r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_iicmpule_r:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_ule r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid
  | ob_by_psub_l:
      forall r op1 op2 retty opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.ipsub r retty opty op1 op2) =
                    Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_psub_r:
      forall r op1 op2 retty opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.ipsub r retty opty op1 op2) =
                    Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid.

(* A value is possibly a guessed pointer if it is a physical pointer. *)
Inductive possibly_guessedptr (v:Ir.val):Prop :=
| pg_phy: forall o I cid (HPHY: v = Ir.ptr (Ir.pphy o I cid)),
    possibly_guessedptr v.

(* Memory access from a possibly guessed pointer if.. *)
Inductive memaccess_from_possibly_guessedptr (md:Ir.IRModule.t) (st:Ir.Config.t)
:Prop :=
  | gp_store:
      forall valty opval opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.istore valty opptr opval) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st
  | gp_load:
      forall retty opval opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.iload retty opval opptr) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st
  | gp_free:
      forall opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.ifree opptr) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st.

Lemma eq_wom_refl:
  forall st1,
    Ir.Config.eq_wom st1 st1.
Proof.
  intros.
  split.
  { apply Ir.Stack.eq_refl.  }
  { split; congruence. }
Qed.

Lemma eq_wom_sym:
  forall st1 st2 (HEQ:Ir.Config.eq_wom st1 st2),
    Ir.Config.eq_wom st2 st1.
Proof.
  intros.
  inv HEQ.
  inv H0.
  split.
  { apply Ir.Stack.eq_symm. eassumption. }
  { split; congruence. }
Qed.

Lemma eq_wom_update_m:
  forall st1 st2 (HEQ:Ir.Config.eq_wom st1 st2) m1 m2,
    Ir.Config.eq_wom (Ir.Config.update_m st1 m1) (Ir.Config.update_m st2 m2).
Proof.
  intros.
  unfold Ir.Config.update_m.
  inv HEQ.
  inv H0.
  unfold Ir.Config.eq_wom.
  simpl.
  split. assumption.
  split; assumption.
Qed.

Lemma twin_state_sym:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid),
    twin_state st2 st1 blkid.
Proof.
  intros.
  inv HTWIN.
  split.
  { apply eq_wom_sym. assumption. }
  inv H0.
  split. congruence.
  inv H2.
  split. congruence.
  inv H3.
  split. congruence.
  intros.
  assert (H4' := H4 bid'). inv H4'. clear H4.
  split.
  { intros HH. subst bid'.
    assert (HH2 := eq_refl blkid).
    apply H3 in HH2.
    destruct HH2 as [mb1 HH2].
    destruct HH2 as [mb2 HH2].
    inv HH2.
    destruct H6.
    destruct H7.
    destruct H8.
    destruct H9.
    destruct H10.
    destruct H11.
    destruct H12.
    exists mb2, mb1.
    repeat (split; try congruence).
    apply Permutation_sym. congruence.
  }
  { intros. apply H5 in HMATCH.
    congruence.
  }
Qed.

Lemma twin_state_get_funid_eq:
  forall (st1 st2:Ir.Config.t) c blkid
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.get_funid st1 c = Ir.Config.get_funid st2 c.
Proof.
  intros.
  unfold Ir.Config.get_funid.
  inv HTWIN.
  inv H.
  inv H2.
  rewrite H.
  reflexivity.
Qed.

Lemma twin_state_cur_fdef_pc_eq:
  forall (md:Ir.IRModule.t) (st1 st2:Ir.Config.t) blkid
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.cur_fdef_pc md st1 = Ir.Config.cur_fdef_pc md st2.
Proof.
  intros.
  dup HTWIN.
  unfold Ir.Config.cur_fdef_pc.
  inv HTWIN.
  inv H0.
  inv H1.
  inv H.
  des_ifs; try (inv H0; fail).
  try ( unfold Ir.Stack.eq in H0; inv H0;
    simpl in H6; inv H6; inv H0;
    rewrite twin_state_get_funid_eq with (st2 := st2) (blkid := blkid) in Heq0;
      try assumption;
    rewrite Heq3 in Heq0; inv Heq0;
    rewrite Heq4 in Heq1; inv Heq1;
    reflexivity
  ).
  { unfold Ir.Stack.eq in H0.
    inv H0.
    simpl in H6.
    inv H6. inv H0.
    rewrite twin_state_get_funid_eq with (st2 := st2) (blkid := blkid) in Heq0;
      try assumption.
    rewrite Heq3 in Heq0. inv Heq0.
    rewrite Heq4 in Heq1. inv Heq1.
  }
  { unfold Ir.Stack.eq in H0.
    inv H0.
    simpl in H6.
    inv H6. inv H0.
    rewrite twin_state_get_funid_eq with (st2 := st2) (blkid := blkid) in Heq0;
      try assumption.
    rewrite Heq3 in Heq0. inv Heq0.
  }
  { unfold Ir.Stack.eq in H0.
    inv H0.
    simpl in H6.
    inv H6. inv H0.
    rewrite twin_state_get_funid_eq with (st2 := st2) (blkid := blkid) in Heq0;
      try assumption.
    rewrite Heq3 in Heq0. inv Heq0.
    rewrite Heq4 in Heq1. inv Heq1.
  }
  { unfold Ir.Stack.eq in H0.
    inv H0.
    simpl in H6.
    inv H6. inv H0.
    rewrite twin_state_get_funid_eq with (st2 := st2) (blkid := blkid) in Heq0;
      try assumption.
    rewrite Heq2 in Heq0. inv Heq0.
  }
Qed.

Lemma twin_state_cur_inst_eq:
  forall (md:Ir.IRModule.t) (st1 st2:Ir.Config.t) blkid
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.cur_inst md st1 = Ir.Config.cur_inst md st2.
Proof.
  intros.
  inv HTWIN.
  unfold Ir.Config.cur_inst.
  inv H.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Stack.eq in H1.
  destruct (Ir.Config.s st1);
    destruct (Ir.Config.s st2).
  { reflexivity. }
  { inv H1. }
  { inv H1. }
  { inv H1. inv H5. inv H1.
    destruct p. destruct p0. simpl in H. subst c.
    simpl in H3.
    destruct p. destruct p0.
    simpl in H3. subst p.
    simpl in H4.
    unfold Ir.Config.get_funid.
    inv H2.
    rewrite H.
    des_ifs.
  }
Qed.

Lemma twin_state_get_val_eq:
  forall (st1 st2:Ir.Config.t) blkid r
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.get_val st1 r = Ir.Config.get_val st2 r.
Proof.
  intros.
  inv HTWIN.
  unfold Ir.Config.get_val.
  destruct r; try reflexivity.
  unfold Ir.Config.get_rval.
  inv H.
  unfold Ir.Stack.eq in H1.
  destruct (Ir.Config.s st1);
    destruct (Ir.Config.s st2).
  { reflexivity. }
  { inv H1. }
  { inv H1. }
  { inv H1. inv H5. inv H1.
    destruct p. destruct p0. simpl in H. subst c.
    simpl in H3.
    destruct p. destruct p0.
    simpl in H3. subst p.
    simpl in H4.
    unfold Ir.Regfile.eq in H4.
    apply H4.
  }
Qed.

Lemma twin_state_update_rval: 
  forall (st1 st2:Ir.Config.t) blkid r v
         (HTWIN:twin_state st1 st2 blkid),
    twin_state (Ir.Config.update_rval st1 r v)
               (Ir.Config.update_rval st2 r v) blkid.
Proof.
  intros.
  inv HTWIN.
  inv H.
  unfold Ir.Config.update_rval.
  des_ifs; try (inv H1; fail).
  { split.
    { split. rewrite Heq, Heq0. assumption.
      assumption. }
    { apply H0. }
  }
  { inv H1.
    simpl in H5. inv H5. inv H1.
    destruct H0.
    destruct H0.
    destruct H1.
    split.
    { split.
      { simpl. unfold Ir.Stack.eq. simpl.
        apply List.Forall2_cons. simpl.
        split. congruence. split . congruence.
        apply Ir.Regfile.update_eq. assumption.
        assumption.
      }
      { assumption. }
    }
    simpl.
    split. congruence.
    split. congruence.
    split. congruence.
    intros.
    assert (H4' := H4 bid'). clear H4.
    split.
    { intros HH. simpl. subst bid'.
      destruct H4'. assert (HDUMMY: blkid = blkid) by reflexivity.
      apply H4 in HDUMMY. clear H4.
      destruct HDUMMY as [mb1 HDUMMY].
      destruct HDUMMY as [mb2 HDUMMY].
      exists mb1. exists mb2.
      assumption.
    }
    { intros HH. destruct H4'.
      apply H5 in HH. assumption.
    }
  }
Qed.

Lemma twin_state_update_pc:
  forall (st1 st2:Ir.Config.t) blkid pc0
         (HTWIN:twin_state st1 st2 blkid),
    twin_state (Ir.Config.update_pc st1 pc0)
               (Ir.Config.update_pc st2 pc0) blkid.
Proof.
  intros.
  inv HTWIN.
  inv H.
  unfold Ir.Config.update_pc.
  des_ifs; try (inv H1; fail).
  { split.
    { split. rewrite Heq, Heq0. assumption.
      assumption. }
    { apply H0. }
  }
  { inv H1.
    simpl in H5. inv H5. inv H1.
    split.
    { split.
      { simpl. unfold Ir.Stack.eq. simpl.
        apply List.Forall2_cons. simpl.
        split. congruence. split . congruence.
        assumption.
        assumption.
      }
      { assumption. }
    }
    simpl in *.
    destruct H0.
    destruct H0.
    destruct H1.
    split. congruence.
    split. congruence.
    split. congruence.
    intros.
    assert (H4' := H4 bid').
    clear H4. destruct H4'.
    split.
    { intros. eauto. }
    { intros. eauto. }
  }
Qed.

Lemma twin_state_incrpc:
  forall md (st1 st2:Ir.Config.t) blkid
         (HTWIN:twin_state st1 st2 blkid),
    twin_state (Ir.SmallStep.incrpc md st1)
               (Ir.SmallStep.incrpc md st2) blkid.
Proof.
  intros.
  dup HTWIN.
  inv HTWIN.
  inv H.
  unfold Ir.SmallStep.incrpc.
  rewrite twin_state_cur_fdef_pc_eq with (st2 := st2) (blkid := blkid);
    try assumption.
  des_ifs; try (inv H1; fail).
  apply twin_state_update_pc.
  assumption.
Qed.

Lemma twin_state_update_reg_and_incrpc:
  forall md (st1 st2:Ir.Config.t) blkid r v
         (HTWIN:twin_state st1 st2 blkid),
    twin_state (Ir.SmallStep.update_reg_and_incrpc md st1 r v)
               (Ir.SmallStep.update_reg_and_incrpc md st2 r v) blkid.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  apply twin_state_incrpc.
  apply twin_state_update_rval.
  assumption.
Qed.

Lemma twin_state_p2N_eq:
  forall st1 st2 b blkid n o
         (HTWIN: twin_state st1 st2 blkid)
         (HNEQ:b <> blkid),
    Ir.SmallStep.p2N (Ir.plog b o) (Ir.Config.m st1) n =
    Ir.SmallStep.p2N (Ir.plog b o) (Ir.Config.m st2) n.
Proof.
  intros.
  inv HTWIN.
  destruct H0.
  destruct H1.
  destruct H2.
  assert (HH := H3 b).
  clear H3.
  destruct HH. clear H3.
  apply H4 in HNEQ. clear H4.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  rewrite HNEQ.
  reflexivity.
Qed.

Lemma twin_state_gep_eq:
  forall st1 st2 b blkid n t o inb
         (HTWIN: twin_state st1 st2 blkid),
    Ir.SmallStep.gep (Ir.plog b o) n t (Ir.Config.m st1) inb =
    Ir.SmallStep.gep (Ir.plog b o) n t (Ir.Config.m st2) inb.
Proof.
  intros.
  destruct HTWIN.
  destruct H0.
  destruct H1.
  destruct H2.
  assert (HH := H3 b).
  clear H3.
  destruct HH.
  destruct (b =? blkid) eqn:HBLKID.
  { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
    dup HBLKID.
    apply H3 in HBLKID.
    subst b.
    clear H3. destruct HBLKID. destruct H3.
    destruct H3.
    destruct H5.
    unfold Ir.SmallStep.gep.
    destruct inb.
    { rewrite <- H3. rewrite <- H5.
      assert (HINB: forall o', Ir.MemBlock.inbounds o' x = Ir.MemBlock.inbounds o' x0).
      { intros.
        unfold Ir.MemBlock.inbounds.
        destruct H6.
        destruct H7.
        destruct H8.
        rewrite H8. reflexivity. }
      rewrite HINB.
      rewrite HINB.
      reflexivity.
    }
    { reflexivity. }
  }
  { unfold Ir.SmallStep.gep.
    rewrite PeanoNat.Nat.eqb_neq in HBLKID.
    apply H4 in HBLKID.
    rewrite HBLKID.
    reflexivity.
  }
Qed.

Lemma twin_state_deref_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid)
         l ofs n,
    Ir.deref (Ir.Config.m st1) (Ir.plog l ofs) n =
    Ir.deref (Ir.Config.m st2) (Ir.plog l ofs) n.
Proof.
  intros.
  unfold Ir.deref.
  unfold Ir.get_deref.
  destruct (l =? blkid) eqn:HBLKID.
  { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
    subst l.
    destruct HTWIN.
    destruct H0.
    destruct H1.
    destruct H2.
    assert (H3' := H3 blkid).
    destruct H3'.
    exploit H4.
    reflexivity.
    intros H4'.
    destruct H4' as [mb1 [mb2 H4']].
    destruct H4' as [HH0 HH1].
    destruct HH1 as [HH1 HH2].
    destruct HH2 as [HH2 HH3].
    destruct HH3 as [HH3 HH4].
    destruct HH4 as [HH4 HH5].
    destruct HH5 as [HH5 HH6].
    rewrite <- HH0.
    rewrite <- HH1.
    unfold Ir.MemBlock.alive.
    unfold Ir.MemBlock.inbounds.
    rewrite HH3.
    rewrite HH4.
    des_ifs.
  }
  { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
    destruct HTWIN.
    destruct H0.
    destruct H1.
    destruct H2.
    assert (H3' := H3 l).
    destruct H3'.
    apply H5 in HBLKID.
    rewrite HBLKID. reflexivity.
  }
Qed. 

Ltac decompose_HTWIN HTWIN blkid :=
        destruct HTWIN as [HTWIN1 HTWIN2];
        destruct HTWIN2 as [HTWIN2 HTWIN3];
        destruct HTWIN3 as [HTWIN3 HTWIN4];
        destruct HTWIN4 as [HTWIN4 HTWIN5];
        assert (HTWIN5' := HTWIN5 blkid).

Ltac decompose_mbs H4':=
    destruct H4' as [mb1 [mb2 H4']];
    destruct H4' as [HH0 HH1];
    destruct HH1 as [HH1 HH2];
    destruct HH2 as [HH2 HH3];
    destruct HH3 as [HH3 HH4];
    destruct HH4 as [HH4 HH5];
    destruct HH5 as [HH5 HH6];
    destruct HH6 as [HH6 HH7].

Ltac decompose_HTWIN' HTWIN blkid :=
  destruct HTWIN as [HTWIN1' HTWIN2']; destruct HTWIN2' as [HTWIN2' HTWIN3'];
   destruct HTWIN3' as [HTWIN3' HTWIN4']; destruct HTWIN4' as [HTWIN4' HTWIN5'];
   pose proof (HTWIN5' blkid) as HTWIN5'.

Ltac decompose_mbs' H4':=
    destruct H4' as [mb1' [mb2' H4'']];
    destruct H4'' as [HH0' HH1'];
    destruct HH1' as [HH1' HH2'];
    destruct HH2' as [HH2' HH3'];
    destruct HH3' as [HH3' HH4'];
    destruct HH4' as [HH4' HH5'];
    destruct HH5' as [HH5' HH6'];
    destruct HH6' as [HH6' HH7'].


Lemma twin_state_load_bytes_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid) l ofs thety,
    Ir.load_bytes (Ir.Config.m st1) (Ir.plog l ofs) thety =
    Ir.load_bytes (Ir.Config.m st2) (Ir.plog l ofs) thety.
Proof.
  intros.
  unfold Ir.load_bytes.
    destruct (Ir.get_deref
                (Ir.Config.m st1) (Ir.plog l ofs) thety)
    eqn:HGD1;
    destruct (Ir.get_deref
                (Ir.Config.m st2) (Ir.plog l ofs) thety)
             eqn:HGD2; try reflexivity.
  { unfold Ir.get_deref in HGD1, HGD2.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      decompose_HTWIN HTWIN blkid.
      destruct HTWIN5'.
      exploit H. reflexivity. intro HH.
      decompose_mbs HH. clear H.
      rewrite <- HH0 in HGD1.
      rewrite <- HH1 in HGD2.
      unfold Ir.MemBlock.alive in *.
      rewrite HH3 in HGD1.
      unfold Ir.MemBlock.inbounds in *.
      rewrite HH4 in HGD1.
      des_ifs.
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      decompose_HTWIN HTWIN l.
      destruct HTWIN5'.
      exploit H0. assumption. intro HH.
      rewrite HH in HGD1. rewrite HGD1 in HGD2. congruence.
    }
  }
  { unfold Ir.get_deref in HGD1, HGD2.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      decompose_HTWIN HTWIN blkid.
      destruct HTWIN5'.
      exploit H. reflexivity. intro HH.
      decompose_mbs HH. clear H.
      rewrite <- HH0 in HGD1.
      rewrite <- HH1 in HGD2.
      unfold Ir.MemBlock.alive in *.
      rewrite HH3 in HGD1.
      unfold Ir.MemBlock.inbounds in *.
      rewrite HH4 in HGD1.
      des_ifs.
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      decompose_HTWIN HTWIN l.
      destruct HTWIN5'.
      exploit H0. assumption. intro HH.
      rewrite HH in HGD1. rewrite HGD1 in HGD2. congruence.
    }
  }
  { unfold Ir.get_deref in HGD1, HGD2.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      decompose_HTWIN HTWIN blkid.
      destruct HTWIN5'.
      exploit H. reflexivity. intro HH.
      decompose_mbs HH.
      unfold Ir.MemBlock.alive in HGD1, HGD2.
      unfold Ir.MemBlock.inbounds in HGD1, HGD2.
      rewrite <- HH0 in HGD1.
      rewrite <- HH1 in HGD2.
      rewrite HH3 in HGD1.
      rewrite HH4 in HGD1.
      des_ifs.
      { unfold Ir.MemBlock.bytes in *.
        rewrite HH6. reflexivity.
      }
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      decompose_HTWIN HTWIN l.
      destruct HTWIN5'.
      exploit H0. assumption. intros HH.
      rewrite HH in HGD1. rewrite HGD1 in HGD2.
      inv HGD2. reflexivity.
    }
  }
Qed.

Lemma twin_state_load_val_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid) l ofs thety,
    Ir.load_val (Ir.Config.m st1) (Ir.plog l ofs) thety =
    Ir.load_val (Ir.Config.m st2) (Ir.plog l ofs) thety.
Proof.
  intros.
  unfold Ir.load_val.
  destruct thety.
  { erewrite twin_state_load_bytes_eq. reflexivity.
    eassumption. }
  { erewrite twin_state_load_bytes_eq. reflexivity.
    eassumption. }
Qed.


Lemma store_val_wf_unfold_int:
  forall st blkid ofs n0 isz mb
         (HDEREF:Ir.deref (Ir.Config.m st) (Ir.plog blkid ofs)
              (length (Ir.Byte.ofint n0 isz)) = true)
         (HTYSZ:Ir.ty_bytesz (Ir.ity isz) = length (Ir.Byte.ofint n0 isz))
         (HGET:Some mb = Ir.Memory.get (Ir.Config.m st) blkid)
         (HSZ:Ir.ty_bytesz (Ir.ity isz) >0)
         (HWF:Ir.Memory.wf
                (Ir.store_val (Ir.Config.m st) (Ir.plog blkid ofs)
                              (Ir.num n0) (Ir.ity isz))),
    Ir.Memory.wf
      (Ir.Memory.set (Ir.Config.m st) blkid
                     (Ir.MemBlock.set_bytes mb ofs (Ir.Byte.ofint n0 isz))).
Proof.
  intros.
  unfold Ir.store_val in HWF.
  unfold Ir.store_bytes in HWF.
  rewrite HTYSZ in HWF. rewrite PeanoNat.Nat.eqb_refl in HWF.
  unfold Ir.deref in HDEREF.
  des_ifs.
  { unfold Ir.get_deref in Heq.
    rewrite <- HGET in Heq.
    des_ifs.
    unfold Ir.MemBlock.inbounds in Heq1.
    rewrite PeanoNat.Nat.ltb_lt in Heq0.
    rewrite PeanoNat.Nat.lt_nge in Heq0.
    rewrite <- PeanoNat.Nat.leb_nle in Heq0.
    rewrite Heq0 in Heq1.
    rewrite andb_false_r in Heq1. congruence.
  }
  { unfold Ir.get_deref in Heq.
    rewrite <- HGET in Heq.
    des_ifs.
  }
Qed.

Lemma store_val_wf_unfold_ptr:
  forall st blkid ofs p mb pt
         (HDEREF:Ir.deref (Ir.Config.m st) (Ir.plog blkid ofs)
              (length (Ir.Byte.ofptr p)) = true)
         (HGET:Some mb = Ir.Memory.get (Ir.Config.m st) blkid)
         (HWF:Ir.Memory.wf
                (Ir.store_val (Ir.Config.m st) (Ir.plog blkid ofs)
                              (Ir.ptr p) (Ir.ptrty pt))),
    Ir.Memory.wf
      (Ir.Memory.set (Ir.Config.m st) blkid
                     (Ir.MemBlock.set_bytes mb ofs (Ir.Byte.ofptr p))).
Proof.
  intros.
  unfold Ir.store_val in HWF.
  unfold Ir.store_bytes in HWF.
  assert (HPLEN:Ir.ty_bytesz (Ir.ptrty pt) =? length (Ir.Byte.ofptr p)).
  { unfold Ir.ty_bytesz.
    unfold Ir.Byte.ofptr.
    unfold Ir.PTRSZ. reflexivity. }
  rewrite HPLEN in HWF.
  unfold Ir.deref in HDEREF.
  des_ifs.
  { unfold Ir.get_deref in Heq.
    rewrite <- HGET in Heq.
    des_ifs.
    unfold Ir.MemBlock.inbounds in Heq1.
    rewrite PeanoNat.Nat.ltb_lt in Heq0.
    rewrite PeanoNat.Nat.lt_nge in Heq0.
    rewrite <- PeanoNat.Nat.leb_nle in Heq0.
    rewrite Heq0 in Heq1.
    rewrite andb_false_r in Heq1. congruence.
  }
  { unfold Ir.get_deref in Heq.
    rewrite <- HGET in Heq.
    des_ifs.
  }
Qed.

Lemma deref_get_some:
  forall m l ofs sz
         (HDEREF:Ir.deref m (Ir.plog l ofs) sz = true),
    exists mb, Ir.Memory.get m l = Some mb.
Proof.
  intros.
  unfold Ir.deref in HDEREF.
  unfold Ir.get_deref in HDEREF.
  des_ifs. eexists. reflexivity.
Qed.

Lemma twin_state_store_val :
  forall md st1 st2 blkid
         (HTWIN:twin_state st1 st2 blkid) l ofs v t
         (HWF1:Ir.Config.wf md st1) (HWF2:Ir.Config.wf md st2)
         (HSZ:Ir.ty_bytesz t > 0)
         (HDEREF:Ir.deref (Ir.Config.m st1) (Ir.plog l ofs) (Ir.ty_bytesz t) = true),
  twin_state
    (Ir.Config.update_m st1 (Ir.store_val (Ir.Config.m st1)
                                                    (Ir.plog l ofs) v t))
    (Ir.Config.update_m st2 (Ir.store_val (Ir.Config.m st2)
                                                    (Ir.plog l ofs) v t))
    blkid.
Proof.
  intros.
  assert (HWF1': Ir.Memory.wf
         (Ir.store_val (Ir.Config.m st1) (Ir.plog l ofs) v t)).
  { apply Ir.store_val_wf.
    { inv HWF1. assumption. }
    { assumption. }
    { assumption. }
  }
  assert (HWF2': Ir.Memory.wf
         (Ir.store_val (Ir.Config.m st2) (Ir.plog l ofs) v t)).  
  { apply Ir.store_val_wf.
    { inv HWF2. assumption. }
    { assumption. }
    { erewrite twin_state_deref_eq in HDEREF.
      eassumption. eassumption. }
  }
  assert (HTWIN_original := HTWIN).
  decompose_HTWIN HTWIN l.
  split.
  { apply eq_wom_update_m. assumption. }
  unfold Ir.store_val.
  unfold Ir.store_bytes.
  split.
  { (* memory time is the same. *)
    unfold Ir.Config.update_m.
    simpl.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      destruct HTWIN5'.
      exploit H. reflexivity. intros HH. clear H H0.
      decompose_mbs HH.
      destruct t.
      { destruct v; try congruence.
        rewrite <- HH0, <- HH1.
        unfold Ir.MemBlock.alive.
        unfold Ir.MemBlock.inbounds.
        rewrite HH3, HH4.
        des_ifs;
        congruence. }
      { destruct v; try congruence.
        { rewrite <- HH0, <- HH1.
          unfold Ir.MemBlock.alive.
          unfold Ir.MemBlock.inbounds.
          rewrite HH3, HH4.
          des_ifs; congruence. }
      }
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      destruct HTWIN5'.
      exploit H0. assumption.
      intros HH.
      destruct t.
      { destruct v; try assumption.
        { rewrite HH.
          des_ifs. }
      }
      { destruct v; try assumption.
        rewrite HH. des_ifs. }
    }
  }
  split.
  { (* call times is the same. *)
    unfold Ir.Config.update_m.
    simpl.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      destruct HTWIN5'.
      exploit H. reflexivity. intros HH. clear H H0.
      decompose_mbs HH.
      destruct t.
      { destruct v; try congruence.
        rewrite <- HH0, <- HH1.
        unfold Ir.MemBlock.alive.
        unfold Ir.MemBlock.inbounds.
        rewrite HH3, HH4.
        des_ifs;
        congruence. }
      { destruct v; try congruence.
        { rewrite <- HH0, <- HH1.
          unfold Ir.MemBlock.alive.
          unfold Ir.MemBlock.inbounds.
          rewrite HH3, HH4.
          des_ifs; congruence. }
      }
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      destruct HTWIN5'.
      exploit H0. assumption.
      intros HH.
      destruct t.
      { destruct v; try assumption.
        { rewrite HH.
          des_ifs. }
      }
      { destruct v; try assumption.
        rewrite HH. des_ifs. }
    }
  }
  split.
  { (* fresh_bid is the same. *)
    unfold Ir.Config.update_m.
    simpl.
    destruct (l =? blkid) eqn:HBLKID.
    { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
      subst l.
      destruct HTWIN5'.
      exploit H. reflexivity. intros HH. clear H H0.
      decompose_mbs HH.
      destruct t.
      { destruct v; try congruence.
        rewrite <- HH0, <- HH1.
        unfold Ir.MemBlock.alive.
        unfold Ir.MemBlock.inbounds.
        rewrite HH3, HH4.
        des_ifs;
        congruence. }
      { destruct v; try congruence.
        { rewrite <- HH0, <- HH1.
          unfold Ir.MemBlock.alive.
          unfold Ir.MemBlock.inbounds.
          rewrite HH3, HH4.
          des_ifs; congruence. }
      }
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
      destruct HTWIN5'.
      exploit H0. assumption.
      intros HH.
      destruct t.
      { destruct v; try assumption.
        { rewrite HH.
          des_ifs. }
      }
      { destruct v; try assumption.
        rewrite HH. des_ifs. }
    }
  }
  clear HTWIN5'.
  split.
  { (* bid' = blkid *)
    intros HEQ.
    repeat (rewrite Ir.Reordering.m_update_m).
    destruct t.
    { destruct v.
      { (* int! *)
        (* Okay, it's talking about l.
         updates bytes of l, and getting blkid. *)
        assert (HTWIN5' := HTWIN5 l).
        destruct (l =? blkid) eqn:HL.
        { rewrite PeanoNat.Nat.eqb_eq in HL.
          destruct HTWIN5'.
          exploit H. assumption. intros HH. clear H H0.
          decompose_mbs HH.
          subst l.
          unfold Ir.get_deref.
          rewrite <- HH0, <- HH1.
          unfold Ir.MemBlock.alive. unfold Ir.MemBlock.inbounds.
          rewrite HH3. rewrite HH4.
          destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint n0 n))
                   eqn:HWELLTYPED;
            destruct (snd (Ir.MemBlock.r mb2)) eqn:HR; simpl.
          { eexists. eexists.
            repeat (split; try eassumption). }
          { destruct ((ofs <=? Ir.MemBlock.n mb2) &&
                      (ofs + length (Ir.Byte.ofint n0 n) <=? Ir.MemBlock.n mb2))
                     eqn:HINB.
            { rewrite andb_true_iff in HINB.
              destruct HINB as [HINB1 HINB2].
              apply leb_complete in HINB2.
              rewrite <- Nat.ltb_ge in HINB2.
              rewrite HH4.
              rewrite HINB2.

              inv HWF1.
              inv HWF2.
              rewrite Ir.Memory.get_set_id with (m := Ir.Config.m st1)
                (mb := mb1) (mb' := Ir.MemBlock.set_bytes mb1 ofs (Ir.Byte.ofint n0 n));
                try eauto.
              rewrite Ir.Memory.get_set_id with (m := Ir.Config.m st2)
                (mb := mb2) (mb' := Ir.MemBlock.set_bytes mb2 ofs (Ir.Byte.ofint n0 n));
                try eauto.
              { eexists. eexists.
                split. reflexivity.
                split. reflexivity.
                repeat (split; unfold Ir.MemBlock.set_bytes; simpl; try congruence).
              }
              { rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF.
                unfold Ir.store_val in HWF2'.
                unfold Ir.store_bytes in HWF2'.
                rewrite HWELLTYPED in HWF2'.
                rewrite PeanoNat.Nat.eqb_eq in HWELLTYPED.
                unfold Ir.deref in HDEREF.
                rewrite HWELLTYPED in HDEREF.
                destruct (Ir.get_deref (Ir.Config.m st2) (Ir.plog blkid ofs)
                         (length (Ir.Byte.ofint n0 n))) eqn:HDEREF'; try congruence.
                unfold Ir.get_deref in HDEREF'. (* get_Deref log is the log. *)
                rewrite <- HH1 in HDEREF'.
                des_ifs.
                repeat (split; try assumption).
              }
              { unfold Ir.store_val in HWF1'.
                unfold Ir.store_bytes in HWF1'.
                rewrite HWELLTYPED in HWF1'.
                rewrite PeanoNat.Nat.eqb_eq in HWELLTYPED.
                unfold Ir.deref in HDEREF.
                rewrite HWELLTYPED in HDEREF.
                destruct (Ir.get_deref (Ir.Config.m st1) (Ir.plog blkid ofs)
                                       (length (Ir.Byte.ofint n0 n)))
                         eqn:HDEREF'; try congruence.
                unfold Ir.get_deref in HDEREF'. (* get_Deref log is the log. *)
                rewrite <- HH0 in HDEREF'.
                unfold Ir.MemBlock.alive in HDEREF'.
                rewrite HH3 in HDEREF'. rewrite HR in HDEREF'.
                unfold Ir.MemBlock.inbounds in HDEREF'.
                rewrite HH4 in HDEREF'. rewrite HINB1 in HDEREF'.
                dup HINB2.
                apply Nat.ltb_ge in HINB2.
                rewrite <- Nat.leb_le in HINB2.
                rewrite HINB2 in HDEREF'.
                inv HDEREF'.
                rewrite HH4 in HWF1'. rewrite HINB0 in HWF1'.
                assumption.
              }
            }
            { (* okay, the inbounds condition is false. *)
              eexists. eexists.
              repeat (split; try eassumption).
            }
          }
          {
            eexists. eexists.
            repeat (split; try eassumption).
          }
          {
            eexists. eexists.
            repeat (split; try eassumption).
          }
        }
        { (* updated block l is different from twn block blkid. *)
          rewrite PeanoNat.Nat.eqb_neq in HL.
          dup HL.
          destruct HTWIN5'. apply H0 in HL. clear H0 H.
          unfold Ir.get_deref.
          rewrite HL.
          (* show that Memory.get l is not None from defef. *)
          assert (HDEREF' := HDEREF).
          rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF';
            try assumption.
          dup HDEREF'.
          unfold Ir.deref in HDEREF'.
          unfold Ir.get_deref in HDEREF'.
          destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint n0 n))
                   eqn:HWELLTYPED.
          { rewrite PeanoNat.Nat.eqb_eq in HWELLTYPED.
            destruct (Ir.Memory.get (Ir.Config.m st2) l)
              as [ | mbl2] eqn:HMBl2; try congruence.
            rewrite HWELLTYPED in HDEREF'.
            destruct (Ir.MemBlock.alive t && Ir.MemBlock.inbounds ofs t &&
                  Ir.MemBlock.inbounds (ofs + length (Ir.Byte.ofint n0 n)) t)
                     eqn:HRANGE; try congruence.
            destruct (Ir.MemBlock.n t <? ofs + length (Ir.Byte.ofint n0 n)).
            { assert (HTWIN5' := HTWIN5 blkid).
              destruct HTWIN5'.
              exploit H. reflexivity. intros HH.
              assumption. }
            { assert (HTWIN5' := HTWIN5 blkid).
              destruct HTWIN5'.
              exploit H. reflexivity. intros HH.
              decompose_mbs HH.

              assert (HGET1:
                        Ir.Memory.get (Ir.Memory.set (Ir.Config.m st1) l
                  (Ir.MemBlock.set_bytes t ofs (Ir.Byte.ofint n0 n))) blkid =
                      Ir.Memory.get (Ir.Config.m st1) blkid).
              { erewrite Ir.Memory.get_set_diff with (bid' := l) (mb := mb1)
                (m := Ir.Config.m st1); try congruence.
                { inv HWF1. assumption. }
                { apply store_val_wf_unfold_int; try congruence. }
                { reflexivity. }
              }
              rewrite HGET1.

              assert (HGET2:
                        Ir.Memory.get (Ir.Memory.set (Ir.Config.m st2) l
                  (Ir.MemBlock.set_bytes t ofs (Ir.Byte.ofint n0 n))) blkid =
                      Ir.Memory.get (Ir.Config.m st2) blkid).
              { erewrite Ir.Memory.get_set_diff with (bid' := l) (mb := mb2)
                (m := Ir.Config.m st2); try congruence.
                { inv HWF2. assumption. }
                { apply store_val_wf_unfold_int; try congruence. }
                { reflexivity. }
              }
              rewrite HGET2.

              apply H. reflexivity.
            }
          }
          { assert (HTWIN5' := HTWIN5 blkid).
            destruct HTWIN5'.
            exploit H. reflexivity. intros HH.
            assumption.
          }
        }
      }
      { assert (HTWIN5' := HTWIN5 bid').
        destruct HTWIN5'. exploit H. congruence. intros HH.
        clear H. decompose_mbs HH.
        exists mb1, mb2.
        repeat (split; try assumption).
      }
      { assert (HTWIN5' := HTWIN5 bid').
        destruct HTWIN5'. exploit H. congruence. intros HH.
        clear H. decompose_mbs HH.
        exists mb1, mb2.
        repeat (split; try assumption).
      }
    }
    {
      destruct v.
      { assert (HTWIN5' := HTWIN5 bid').
        destruct HTWIN5'. exploit H. congruence. intros HH.
        clear H. decompose_mbs HH.
        exists mb1, mb2.
        repeat (split; try assumption).
      }
      { (* pointer! *)
        assert (HPLEN:Ir.ty_bytesz (Ir.ptrty t) = length (Ir.Byte.ofptr p)).
        { unfold Ir.ty_bytesz.
          unfold Ir.ty_bitsz.
          unfold Ir.Byte.ofptr.
          unfold Ir.PTRSZ.
          reflexivity. }
        assert (HTWIN5' := HTWIN5 l).
        destruct (l =? blkid) eqn:HL.
        { (* modiifed block is the twin block. *)
          rewrite PeanoNat.Nat.eqb_eq in HL.
          destruct HTWIN5'.
          exploit H. assumption. intros HH. clear H H0.
          decompose_mbs HH.
          subst l.
          unfold Ir.get_deref.
          rewrite <- HH0, <- HH1.
          unfold Ir.MemBlock.alive. unfold Ir.MemBlock.inbounds.
          rewrite HH3. rewrite HH4.
          rewrite HPLEN. rewrite PeanoNat.Nat.eqb_refl.
          destruct (snd (Ir.MemBlock.r mb2)) eqn:HR; simpl.
          { eexists. eexists.
            repeat (split; try eassumption). }
          destruct ((ofs <=? Ir.MemBlock.n mb2) &&
                    (ofs + length (Ir.Byte.ofptr p) <=? Ir.MemBlock.n mb2))
                     eqn:HINB.
          { rewrite andb_true_iff in HINB.
            destruct HINB as [HINB1 HINB2].
            assert (HPLEN':length (Ir.Byte.ofptr p) = 2).
            { unfold Ir.Byte.ofptr. unfold Ir.PTRSZ. reflexivity. }
            rewrite HPLEN' in *.
            rewrite HINB1.
            unfold Ir.PTRSZ in HINB2. simpl in HINB2.
            rewrite HINB2.
            simpl.
            apply leb_complete in HINB2.
            rewrite <- Nat.ltb_ge in HINB2.
            rewrite HH4.
            rewrite HINB2.

            inv HWF1.
            inv HWF2.
            rewrite Ir.Memory.get_set_id with (m := Ir.Config.m st1)
                (mb := mb1) (mb' := Ir.MemBlock.set_bytes mb1 ofs (Ir.Byte.ofptr p));
                try eauto.
            rewrite Ir.Memory.get_set_id with (m := Ir.Config.m st2)
                (mb := mb2) (mb' := Ir.MemBlock.set_bytes mb2 ofs (Ir.Byte.ofptr p));
                try eauto.
            { eexists. eexists.
              split. reflexivity.
              split. reflexivity.
              repeat (split; unfold Ir.MemBlock.set_bytes; simpl; try congruence).
            }
            { eapply store_val_wf_unfold_ptr; try congruence.
              { rewrite HPLEN in HDEREF.
                unfold Ir.Byte.ofptr. unfold Ir.PTRSZ. simpl.
                rewrite twin_state_deref_eq with (st2 := st2)
                                                 (blkid := blkid) in HDEREF;
                  try assumption.
              }
              { eassumption. }
            }
            { eapply store_val_wf_unfold_ptr; try congruence.
              { eassumption. }
            }
          }
          { unfold Ir.Byte.ofptr in HINB.
            unfold Ir.PTRSZ in HINB.
            simpl in HINB.
            rewrite HINB.
            assert (HTWIN5' := HTWIN5 blkid).
            destruct HTWIN5'.
            exploit H. reflexivity. intros HH.
            assumption.
          }
        }
        { (* moified block isnt' the twin block *)
          rewrite HPLEN. rewrite PeanoNat.Nat.eqb_refl.
          rewrite HPLEN in HDEREF.
          assert (HDEREF' := HDEREF).
          rewrite PeanoNat.Nat.eqb_neq in HL.
          destruct HTWIN5'.
          dup HL.
          apply H0 in HL0.
          clear H H0.
          unfold Ir.get_deref.
          rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF';
            try assumption.
          dup HDEREF.
          apply deref_get_some in HDEREF0.
          destruct HDEREF0 as [mb1 HGET].
          rewrite <- HL0.
          rewrite HGET.
          des_ifs.
          { assert (HTWIN5' := HTWIN5 blkid). destruct HTWIN5' as [H1 H2].
            exploit H1. reflexivity. intros HH.
            apply HH. }
          { assert (HTWIN5' := HTWIN5 blkid). destruct HTWIN5' as [H1 H2].
            exploit H1. reflexivity. intros HH.
            apply HH. }
          { assert (HTWIN5' := HTWIN5 blkid). destruct HTWIN5' as [H1 H2].
            exploit H1. reflexivity. intros HH. clear H1 H2.
            decompose_mbs HH.
            assert (HGET1:Ir.Memory.get
                      (Ir.Memory.set (Ir.Config.m st1) b
                                     (Ir.MemBlock.set_bytes t0 n (Ir.Byte.ofptr p)))
                      blkid =
                    Ir.Memory.get (Ir.Config.m st1) blkid).
            { erewrite Ir.Memory.get_set_diff with (bid' := b) (mb := mb1)
                (m := Ir.Config.m st1); try congruence.
              { inv HWF1. assumption. }
              { eapply store_val_wf_unfold_ptr; try congruence. eassumption. }
              { reflexivity. }
            }
            assert (HGET2:Ir.Memory.get
                      (Ir.Memory.set (Ir.Config.m st2) b
                                     (Ir.MemBlock.set_bytes t0 n (Ir.Byte.ofptr p)))
                      blkid =
                    Ir.Memory.get (Ir.Config.m st2) blkid).
            { erewrite Ir.Memory.get_set_diff with (bid' := b) (mb := mb2)
                (m := Ir.Config.m st2); try congruence.
              { inv HWF2. assumption. }
              { eapply store_val_wf_unfold_ptr; try congruence. eassumption. }
              { reflexivity. }
            }
            rewrite HGET1, HGET2.
            eexists. eexists.
            repeat (split; try eassumption).
          }
        }
      }
      { assert (HTWIN5' := HTWIN5 bid').
        destruct HTWIN5'. exploit H. congruence. intros HH.
        clear H. decompose_mbs HH.
        exists mb1, mb2.
        repeat (split; try assumption).
      }
    }
  }
  { (* the two blocks bid' & blkid aren't the same. *)
    intros.
    repeat (rewrite Ir.Reordering.m_update_m).
    assert (HTWIN5' := HTWIN5 bid').
    destruct t.
    { destruct HTWIN5'. exploit H0. assumption. intros HH.
      clear H H0.
      destruct v; try assumption.

      destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint n0 n))
               eqn:HWELLTYPED; try assumption.
      rewrite PeanoNat.Nat.eqb_eq in HWELLTYPED.

      (* Okay, the block l can be the blkid or not. *)
      destruct (l =? blkid) eqn:HBLKID.
      { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
        assert (HTWIN5' := HTWIN5 l).
        destruct HTWIN5'. exploit H. assumption. intros HH2. clear H H0.
        decompose_mbs HH2.
        unfold Ir.get_deref.
        unfold Ir.MemBlock.alive, Ir.MemBlock.inbounds.
        subst l.
        rewrite <- HH0, <- HH1.
        rewrite HH3, HH4.
        des_ifs.
        { rewrite HH4 in Heq0. congruence. }
        { rewrite HH4 in Heq0. congruence. }
        { rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { apply store_val_wf_unfold_int; try assumption.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := b) in HDEREF.
            assumption.
            assumption. }
          { inv HWF1. assumption. }
          { apply store_val_wf_unfold_int; try assumption.
            rewrite <- HWELLTYPED. assumption. }
        }
      }
      { (* the dereferenced lbock isn't blkid! *)
        rewrite PeanoNat.Nat.eqb_neq in HBLKID.
        assert (HTWIN5' := HTWIN5 l).
        destruct HTWIN5'. exploit H0. assumption. intros HH2. clear H H0.
        unfold Ir.get_deref.
        rewrite HH2.
        des_ifs.
        (* but.. b may equal to bid'. *)
        destruct (b =? bid') eqn:HBID'.
        { rewrite PeanoNat.Nat.eqb_eq in HBID'.
          subst b.
          rewrite Ir.Memory.get_set_id_short with (mb0 := t); try assumption.
          rewrite Ir.Memory.get_set_id_short with (mb0 := t); try assumption.
          reflexivity.
          { inv HWF2. assumption. }
          { apply store_val_wf_unfold_int; try congruence.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF.
            assumption.
            assumption. }
          { inv HWF1. assumption. }
          { apply store_val_wf_unfold_int; try congruence. }
        }
        { rewrite PeanoNat.Nat.eqb_neq in HBID'.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { apply store_val_wf_unfold_int; try congruence.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF.
            assumption.
            assumption. }
          { congruence. }
          { inv HWF1. assumption. }
          { apply store_val_wf_unfold_int; try congruence. }
          { congruence. }
        }
      }
    }
    { (* pointer. *)
      destruct HTWIN5'. exploit H0. assumption. intros HH.
      clear H H0.
      destruct v; try assumption.

      assert (HWELLTYPED:Ir.ty_bytesz (Ir.ptrty t) =? length (Ir.Byte.ofptr p)).
      { unfold Ir.ty_bytesz. unfold Ir.Byte.ofptr. 
        unfold Ir.ty_bitsz. unfold Ir.PTRSZ. reflexivity. }

      (* Okay, the block l can be the blkid or not. *)
      destruct (l =? blkid) eqn:HBLKID.
      { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
        assert (HTWIN5' := HTWIN5 l).
        destruct HTWIN5'. exploit H. assumption. intros HH2. clear H H0.
        decompose_mbs HH2.
        unfold Ir.get_deref.
        unfold Ir.MemBlock.alive, Ir.MemBlock.inbounds.
        subst l.
        rewrite <- HH0, <- HH1.
        rewrite HH3, HH4.
        des_ifs.
        { rewrite HH4 in Heq0. congruence. }
        { rewrite HH4 in Heq0. congruence. }
        { rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { eapply store_val_wf_unfold_ptr; try assumption.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := b) in HDEREF.
            assumption.
            assumption. }
          { inv HWF1. assumption. }
          { eapply store_val_wf_unfold_ptr; try assumption. }
        }
      }
      { (* the dereferenced block isn't blkid! *)
        rewrite PeanoNat.Nat.eqb_neq in HBLKID.
        assert (HTWIN5' := HTWIN5 l).
        destruct HTWIN5'. exploit H0. assumption. intros HH2. clear H H0.
        unfold Ir.get_deref.
        rewrite HH2.
        des_ifs.
        (* but.. b may equal to bid'. *)
        destruct (b =? bid') eqn:HBID'.
        { rewrite PeanoNat.Nat.eqb_eq in HBID'.
          subst b.
          rewrite Ir.Memory.get_set_id_short with (mb0 := t0); try assumption.
          rewrite Ir.Memory.get_set_id_short with (mb0 := t0); try assumption.
          reflexivity.
          { inv HWF2. assumption. }
          { eapply store_val_wf_unfold_ptr; try congruence.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF.
            assumption.
            assumption.
            eassumption. }
          { inv HWF1. assumption. }
          { eapply store_val_wf_unfold_ptr; try congruence.
            rewrite <- HWELLTYPED. assumption.
          eassumption. }
        }
        { rewrite PeanoNat.Nat.eqb_neq in HBID'.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { eapply store_val_wf_unfold_ptr; try congruence.
            rewrite <- HWELLTYPED.
            rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF.
            assumption.
            assumption. eassumption. }
          { congruence. }
          { inv HWF1. assumption. }
          { eapply store_val_wf_unfold_ptr; try congruence.
          rewrite <- HWELLTYPED. assumption.
          eassumption. }
          { congruence. }
        }
      }
    }
  }
  Unshelve. assumption. assumption.
Qed.


Lemma twin_state_free:
  forall l ofs st1 st2 blkid md
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (HTWIN:twin_state st1 st2 blkid),
    (exists m1 m2,
        Some m1 = (Ir.SmallStep.free (Ir.plog l ofs) (Ir.Config.m st1)) /\
        Some m2 = (Ir.SmallStep.free (Ir.plog l ofs) (Ir.Config.m st2)) /\
        twin_state (Ir.Config.update_m st1 m1)
                   (Ir.Config.update_m st2 m2)
                   blkid)
      \/
    None = Ir.SmallStep.free (Ir.plog l ofs) (Ir.Config.m st1) /\
    None = Ir.SmallStep.free (Ir.plog l ofs) (Ir.Config.m st2).
Proof.
  intros.
  unfold Ir.SmallStep.free.
  destruct ofs; try (right; split; reflexivity).
  unfold Ir.Memory.free.
  destruct (l =? blkid) eqn:HBLKID.
  { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
    decompose_HTWIN HTWIN blkid.
    destruct HTWIN5'. clear H0.
    exploit H. reflexivity. intros HH. clear H.
    decompose_mbs HH.
    subst l.
    rewrite <- HH0, <- HH1.
    unfold Ir.MemBlock.set_lifetime_end.
    unfold Ir.MemBlock.alive.
    rewrite HH2.
    destruct (Ir.MemBlock.bt mb2) eqn:HBT2; try (right; split ;reflexivity).
    rewrite HH3.
    destruct (snd (Ir.MemBlock.r mb2)) eqn:HR; try (right; split; reflexivity).
    rewrite <- HH3.
    left.
    eexists. eexists.
    split. reflexivity.
    split. reflexivity.
    split.
    { apply eq_wom_update_m. assumption. }
    split.
    { rewrite Ir.Reordering.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { rewrite Ir.Reordering.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { rewrite Ir.Reordering.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { inv HWF1.
      intros. subst bid'.
      rewrite Ir.Reordering.m_update_m.
      eexists. eexists.
      split.
      { erewrite Ir.Memory.get_set_id_short.
        { reflexivity. }
        { eapply Ir.Memory.incr_time_wf.
          eassumption. reflexivity.
        }
        { rewrite Ir.Memory.get_incr_time_id. rewrite HH0. reflexivity. }
        { eapply Ir.Memory.free_wf with (m := Ir.Config.m st1).
          eassumption.
          unfold Ir.Memory.free.
          rewrite <- HH0. rewrite HH2.
          rewrite <- HH3 in HR.
          unfold Ir.MemBlock.set_lifetime_end.
          unfold Ir.MemBlock.alive. rewrite HR.
          rewrite HH2. reflexivity.
        }
      }
      split.
      { rewrite Ir.Reordering.m_update_m.
        erewrite Ir.Memory.get_set_id_short.
        { reflexivity. }
        { inv HWF2. eapply Ir.Memory.incr_time_wf. eassumption.
          reflexivity. }
        { rewrite HH1. reflexivity. }
        { inv HWF2.
          eapply Ir.Memory.free_wf with (m := Ir.Config.m st2).
          eassumption.
          unfold Ir.Memory.free.
          rewrite <- HH1. rewrite <- HH2.
          unfold Ir.MemBlock.set_lifetime_end.
          unfold Ir.MemBlock.alive. rewrite HR.
          rewrite HH3, HH2, HBT2.
          reflexivity.
        }
      }
      repeat (split; simpl; try congruence).
    }
    { (*bid' is not blkid. *)
      intros HDIFF.
      dup HDIFF.
      assert (HTWIN5' := HTWIN5 bid').
      destruct HTWIN5'. apply H0 in HDIFF. clear H H0.
      rewrite Ir.Reordering.m_update_m.
      rewrite Ir.Reordering.m_update_m.
      rewrite Ir.Memory.get_set_diff_short.
      rewrite Ir.Memory.get_set_diff_short.
      { unfold Ir.Memory.get.
        unfold Ir.Memory.get in HDIFF.
        unfold Ir.Memory.incr_time.
        simpl. assumption. }
      { inv HWF2.
        eapply Ir.Memory.incr_time_wf.
        eapply wf_m. reflexivity. }
      { inv HWF2.
        eapply Ir.Memory.free_wf with (m := Ir.Config.m st2).
        eassumption.
        unfold Ir.Memory.free.
        rewrite <- HH1. rewrite <- HH2.
        unfold Ir.MemBlock.set_lifetime_end.
        unfold Ir.MemBlock.alive. rewrite HR.
        rewrite HH3, HH2, HBT2.
        reflexivity.
      }
      { assumption. }
      { inv HWF1.
        eapply Ir.Memory.incr_time_wf.
        eassumption. reflexivity.
      }
      { inv HWF1.
        eapply Ir.Memory.free_wf with (m := Ir.Config.m st1).
        eassumption.
        unfold Ir.Memory.free.
        rewrite <- HH0. rewrite HH2.
        rewrite <- HH3 in HR.
        unfold Ir.MemBlock.set_lifetime_end.
        unfold Ir.MemBlock.alive. rewrite HR.
        rewrite HH2. reflexivity.
      }
      { assumption. }
    }
  }
  { (* freed block l is not twin block blkid. *)
    rewrite PeanoNat.Nat.eqb_neq in HBLKID.
    decompose_HTWIN HTWIN l.
    destruct HTWIN5'. clear H.
    exploit H0. congruence. intros HH. clear H0.
    rewrite HH.
    destruct (Ir.Memory.get (Ir.Config.m st1) l) eqn:HGET1;
      try (right; rewrite <- HH; split; reflexivity).
    rewrite <- HH.
    destruct (Ir.MemBlock.bt t) eqn:HBT;
      try (right; split; reflexivity).
    destruct (Ir.MemBlock.alive t) eqn:HALIVE;
      try (right; split; reflexivity).
    unfold Ir.MemBlock.set_lifetime_end.
    rewrite HALIVE.
    left. eexists. eexists.
    split. reflexivity.
    split. reflexivity.
    split.
    { eassumption. }
    split. rewrite Ir.Reordering.m_update_m. simpl. congruence.
    split. rewrite Ir.Reordering.m_update_m. simpl. congruence.
    split. rewrite Ir.Reordering.m_update_m. simpl. congruence.
    split.
    { intros HDIFF2.
      subst bid'.
      rewrite Ir.Reordering.m_update_m.
      rewrite Ir.Reordering.m_update_m.
      (* okay,, exploit HTWIN5 again *)
      assert (HTWIN5' := HTWIN5 blkid).
      destruct HTWIN5'. clear H0. exploit H.
      reflexivity. intros HH2. clear H.
      decompose_mbs HH2.
      rewrite HBT.
      exists mb1. exists mb2.
      split.
      { erewrite Ir.Memory.get_set_diff_short; try eassumption.
        { inv HWF1.
          eapply Ir.Memory.incr_time_wf. eassumption.
          reflexivity. }
        { inv HWF1.
          eapply Ir.Memory.free_wf. eapply wf_m.
          unfold Ir.Memory.free. rewrite HGET1.
          rewrite HBT. unfold Ir.MemBlock.set_lifetime_end.
          rewrite HALIVE. congruence. }
        { congruence. }
      }
      split.
      { erewrite Ir.Memory.get_set_diff_short; try eassumption.
        { inv HWF2.
          eapply Ir.Memory.incr_time_wf. eassumption.
          reflexivity. }
        { inv HWF2.
          eapply Ir.Memory.free_wf. eapply wf_m.
          unfold Ir.Memory.free. rewrite <- HH.
          rewrite HBT. unfold Ir.MemBlock.set_lifetime_end.
          rewrite HALIVE. congruence. }
        { congruence. }
      }
      repeat (split; try congruence).
    }
    { intros HDIFF2.
      rewrite Ir.Reordering.m_update_m.
      rewrite Ir.Reordering.m_update_m.
      destruct (l =? bid') eqn:HBID'.
      { rewrite PeanoNat.Nat.eqb_eq in HBID'.
        subst l.
        erewrite Ir.Memory.get_set_id_short.
        erewrite Ir.Memory.get_set_id_short.
        { rewrite HTWIN2. reflexivity. }
        { inv HWF2.
          eapply Ir.Memory.incr_time_wf.
          eassumption. reflexivity. }
        { rewrite Ir.Memory.get_incr_time_id. rewrite HH. reflexivity. }
        { inv HWF2.
          eapply Ir.Memory.free_wf.
          { eassumption. }
          { unfold Ir.Memory.free. rewrite <- HH.
            unfold Ir.MemBlock.set_lifetime_end.
            rewrite HBT, HALIVE.
            congruence.
          }
        }
        { inv HWF1.
          eapply Ir.Memory.incr_time_wf.
          eassumption. reflexivity. }
        { rewrite Ir.Memory.get_incr_time_id. rewrite HGET1. reflexivity. }
        { inv HWF1.
          eapply Ir.Memory.free_wf.
          { eassumption. }
          { unfold Ir.Memory.free. rewrite HGET1.
            unfold Ir.MemBlock.set_lifetime_end.
            rewrite HBT, HALIVE.
            congruence.
          }
        }
      }
      { (* freeing block isn't bid. *)
        rewrite PeanoNat.Nat.eqb_neq in HBID'.
        assert (HTWIN5' := HTWIN5 bid').
        destruct HTWIN5'. exploit H0. assumption.
        intros HH0. clear H0 H.
        rewrite Ir.Memory.get_set_diff_short.
        rewrite Ir.Memory.get_set_diff_short.
        rewrite Ir.Memory.get_incr_time_id.
        rewrite Ir.Memory.get_incr_time_id.
        congruence.
        { inv HWF2.
          eapply Ir.Memory.incr_time_wf; eauto. }
        { inv HWF2.
          eapply Ir.Memory.free_wf; eauto.
          unfold Ir.Memory.free.
          rewrite <- HH.
          rewrite HBT.
          unfold Ir.MemBlock.set_lifetime_end.
          rewrite HALIVE.
          congruence. }
        { congruence. }
        { inv HWF1.
          eapply Ir.Memory.incr_time_wf; eauto. }
        { inv HWF1.
          eapply Ir.Memory.free_wf; eauto.
          unfold Ir.Memory.free.
          rewrite HGET1.
          rewrite HBT.
          unfold Ir.MemBlock.set_lifetime_end.
          rewrite HALIVE.
          congruence. }
        { congruence. }
      }
    }
  }
Qed.


Lemma twin_state_icmp_eq_ptr_nondet_cond_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid) p1 p2,
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st1) = 
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st2).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  destruct p1.
  { (* block id is b. *)
    dup HTWIN.
    decompose_HTWIN HTWIN b.
    destruct (b =? blkid) eqn:HB1.
    { (* okay, b is the twin. *)
      rewrite PeanoNat.Nat.eqb_eq in HB1. dup HB1.
      destruct HTWIN5'. apply H in HB1. clear H0 H.
      decompose_mbs HB1. subst b. rewrite <- HH0. rewrite <- HH1.

      (* next. *)
      destruct p2 as [b2 o2 | ]; try reflexivity.
      (* block id is log b2 again. *)

      decompose_HTWIN' HTWIN0 b2.
      destruct (b2 =? blkid) eqn:HB2.
      { (* oh, op2 is also twin. *)
        rewrite PeanoNat.Nat.eqb_eq in HB2. dup HB2.
        destruct HTWIN5'. exploit H. assumption. intros HH.
        clear H H0. decompose_mbs' HH.
        subst b2.
        rewrite <- HH0'. rewrite <- HH1'.
        rewrite HH3, HH4, HH3', HH4'. reflexivity.
      }
      { (* op2 is not twin. *)
        rewrite PeanoNat.Nat.eqb_neq in HB2. dup HB2.
        destruct HTWIN5'. exploit H0. congruence. intros HH.
          clear H H0. rewrite HH.
          rewrite HH3, HH4. reflexivity.
      }
    }
    { (* b is not a twin. *)
      rewrite PeanoNat.Nat.eqb_neq in HB1. dup HB1.
      destruct HTWIN5'. exploit H0. congruence. intros HH.
      clear H H0. rewrite HH.

      (* next. *)
      destruct p2 as [b2 o2 | ]; try reflexivity.
      decompose_HTWIN' HTWIN0 b2.
      destruct (b2 =? blkid) eqn:HB2.
      { (* oh, op2 is also twin. *)
        rewrite PeanoNat.Nat.eqb_eq in HB2. dup HB2.
        destruct HTWIN5'. exploit H. assumption. intros HH'.
        clear H H0. decompose_mbs' HH'.
        subst b2.
        rewrite <- HH0'. rewrite <- HH1'.
        rewrite HH3', HH4'. reflexivity.
      }
      { (* op2 is not twin. *)
        rewrite PeanoNat.Nat.eqb_neq in HB2. dup HB2.
        destruct HTWIN5'. exploit H0. congruence. intros HH'.
          clear H H0. rewrite HH'. reflexivity.
      }
    }
  } reflexivity.
Qed.

Lemma twin_state_icmp_ule_ptr_nondet_cond_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid) p1 p2,
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st1) = 
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st2).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
  destruct p1.
  { (* block id is b. *)
    dup HTWIN.
    decompose_HTWIN HTWIN b.
    destruct (b =? blkid) eqn:HB1.
    { (* okay, b is the twin. *)
      rewrite PeanoNat.Nat.eqb_eq in HB1. dup HB1.
      destruct HTWIN5'. apply H in HB1. clear H0 H.
      decompose_mbs HB1. subst b. rewrite <- HH0. rewrite <- HH1.

      (* next. *)
      destruct p2 as [b2 o2 | ]; try reflexivity.
      rewrite HH4. reflexivity.
    }
    { (* b is not a twin. *)
      rewrite PeanoNat.Nat.eqb_neq in HB1. dup HB1.
      destruct HTWIN5'. exploit H0. congruence. intros HH.
      clear H H0. rewrite HH.

      (* next. *)
      destruct p2 as [b2 o2 | ]; try reflexivity.
    }
  } reflexivity.
Qed.


(*******************************************************
                 Main Theorems 
 *******************************************************)

Lemma regfile_get_update:
  forall rf r v,
    Ir.Regfile.get (Ir.Regfile.update rf r v) r = Some v.
Proof.
  intros.
  unfold Ir.Regfile.get.
  unfold Ir.Regfile.update.
  unfold list_find_key.
  simpl.
  rewrite PeanoNat.Nat.eqb_refl. reflexivity.
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
  { simpl. apply regfile_get_update. }
  { simpl.
    des_ifs.
    - simpl in Heq. inv Heq. apply regfile_get_update.
    - simpl in Heq. inv Heq. apply regfile_get_update.
    - simpl in Heq. inv Heq. apply regfile_get_update.
  }
Qed.  

Lemma disjoint_range_sym:
  forall r1 r2, disjoint_range r1 r2 = disjoint_range r2 r1.
Proof.
  intros. unfold disjoint_range.
  destruct r1. destruct r2.
  intuition.
Qed.

(* If malloc succeeds, it always creates twin-state. *)
Theorem malloc_creates_twin_state:
  forall (md:Ir.IRModule.t) (st st'1: Ir.Config.t) r retty opsz e'1
         (HCUR: Some (Ir.Inst.imalloc r retty opsz) = Ir.Config.cur_inst md st)
         (HNEXT: Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success e'1 st'1)),
    (* malloc can return NULL, or *)
    Some (Ir.ptr (Ir.NULL)) = Ir.Config.get_val st'1 (Ir.opreg r) \/
    (* malloc reutrn (bid, 0), and malloc can nondeterministically make
       twin state with respect to bid as well *)
    exists st'2 bid,
      Some (Ir.ptr (Ir.plog bid 0)) = Ir.Config.get_val st'1 (Ir.opreg r) /\
      Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success e'1 st'2) /\
      twin_state st'1 st'2 bid.
Proof.
  intros.
  assert (HSTACK:Ir.Config.s st <> []).
  { unfold Ir.Config.cur_inst in HCUR.
    unfold Ir.Config.cur_fdef_pc in HCUR.
    des_ifs. }
  inv HNEXT.
  { unfold Ir.SmallStep.inst_det_step in HNEXT0.
    des_ifs. }
  { (* returned NULL*)
    left.
    rewrite <- HCUR in HCUR0. inv HCUR0.
    rewrite get_val_update_reg_and_incrpc_samereg. reflexivity. assumption. }
  { (* malloc succeeded. *)
    right.
    rewrite <- HCUR in HCUR0.
    inv HCUR0.
    (* Let's make P' which is permutated P. *)
    dup HMBWF.
    assert (HMBWF' := HMBWF (Ir.Memory.mt (Ir.Config.m st))).
    clear HMBWF.
    inv HMBWF'.
    rewrite get_val_update_reg_and_incrpc_samereg.
    simpl in *.
    destruct P as [ | p1 P]; try (inv wf_twin; fail).
    destruct P as [ | p2 P]; try (inv wf_twin; fail).
    exists (Ir.SmallStep.update_reg_and_incrpc md
        (Ir.Config.update_m st
          (fst (Ir.Memory.new (Ir.Config.m st) (Ir.heap) (N.to_nat nsz)
                       (Ir.SYSALIGN) (List.repeat Ir.Byte.poison (N.to_nat nsz))
                       (p2::p1::P))))
        r (Ir.ptr (Ir.plog l 0))).
    exists l.
    split.
    { reflexivity. }
    split.
    { eapply Ir.SmallStep.s_malloc with (P := p2::p1::P).
      eassumption. reflexivity. eassumption. eassumption. reflexivity.
      { clear wf_tcond.
        clear wf_poslen wf_align wf_inmem wf_notnull wf_disj wf_twin.
        intros.
        assert (HMBWF0' := HMBWF0 begt).
        inv HMBWF0'.
        simpl in *.
        split.
        { intros. simpl in *. congruence. }
        { simpl. assumption. }
        { simpl. assumption. }
        { simpl. intros.
          apply wf_align. intuition. }
        { simpl. intros. apply wf_inmem. intuition. }
        { simpl. intros. apply wf_notnull. intuition. }
        { simpl. repeat (rewrite andb_true_iff).
          repeat (rewrite andb_true_iff in wf_disj).
          inv wf_disj. inv H. inv H0.
          split.
          split.
          { rewrite disjoint_range_sym. assumption. }
          { assumption. }
          split.
          { assumption. }
          { assumption. }
        }
        { simpl. assumption. }
      }
      { unfold Ir.Memory.allocatable in *.
        simpl in HDISJ.
        simpl.
        { simpl. repeat (rewrite andb_true_iff).
          repeat (rewrite andb_true_iff in HDISJ).
          inv HDISJ. inv H. inv H0.
          split.
          split.
          { rewrite disjoint_range_sym. assumption. }
          { assumption. }
          split.
          { assumption. }
          { assumption. }
        }
      }
      { unfold Ir.Memory.new.
        simpl.
        unfold Ir.Memory.new in HNEW.
        inv HNEW.
        reflexivity.
      }
    }
    { unfold Ir.Memory.new in HNEW.
      inv HNEW.
      simpl.
      unfold twin_state.
      split.
      { 
        rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
        rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
        apply eq_wom_update_m.
        apply eq_wom_refl.
      }
      { repeat (rewrite Ir.Reordering.update_reg_and_incrpc_update_m).
        repeat (rewrite Ir.Reordering.m_update_m).
        simpl.
        split. reflexivity.
        split. reflexivity.
        split. reflexivity.
        split.
        { intros H0.
          subst bid'.
          eexists. eexists.
          split.
          { unfold Ir.Memory.get.
            simpl. rewrite PeanoNat.Nat.eqb_refl. reflexivity. }
          split.
          { unfold Ir.Memory.get. simpl.
            rewrite PeanoNat.Nat.eqb_refl. reflexivity. }
          simpl.
          split. reflexivity.
          split. reflexivity.
          split. reflexivity.
          split. reflexivity.
          split. reflexivity.
          split. apply perm_swap.
          { (* p1 <> p2 comes from wf_disj. *)
            simpl in wf_disj.
            rewrite andb_true_iff in wf_disj.
            rewrite andb_true_iff in wf_disj.
            rewrite andb_true_iff in wf_disj.
            inv wf_disj. inv H.
            unfold disjoint_range in H1.
            rewrite orb_true_iff in H1.
            rewrite Nat.leb_le in H1.
            rewrite Nat.leb_le in H1.
            destruct (N.to_nat nsz). omega.
            rewrite Nat.add_succ_r in H1.
            rewrite Nat.add_succ_r in H1.
            rewrite Nat.le_succ_l in H1.
            rewrite Nat.le_succ_l in H1.
            omega.
          }
        }
        { intros.
          unfold Ir.Memory.get.
          simpl. apply not_eq_sym in HMATCH.
          rewrite <- PeanoNat.Nat.eqb_neq in HMATCH.
          rewrite HMATCH.
          reflexivity.
        }
      }
    }
    unfold Ir.Config.update_m.
    simpl. assumption.
  }
  { rewrite <- HCUR in HCUR0. congruence. }
  { rewrite <- HCUR in HCUR0. congruence. }
Qed.
      

Ltac thats_it := apply twin_state_update_reg_and_incrpc;
            assumption.

Ltac coalesce_op Hop1 Hop2 st2 HTWIN :=
  assert (Htmp := Hop1);
  assert (Htmp2 := Hop2);
  erewrite twin_state_get_val_eq with (st2 := st2) in Htmp;
  try apply HTWIN;
  rewrite Htmp in Htmp2; inv Htmp2; clear Htmp.

Lemma lt_gt:
  forall n1 n2, n1 < n2 -> n2 > n1.
Proof. intros . omega. Qed.

Lemma ty_bytesz_pos:
  forall t, Ir.ty_bytesz t > 0.
Proof.
  intros.
  unfold Ir.ty_bytesz.
  destruct t.
  { destruct n.
    { simpl. omega. }
    { unfold Ir.ty_bitsz.
      apply lt_gt.
      rewrite Nat.div_str_pos_iff.
      omega.
      omega.
    }
  }
  { unfold Ir.ty_bitsz.
    unfold Ir.PTRSZ. simpl. omega.
  }
Qed.


Lemma twin_state_allocatable_eq:
  forall st1 st2 blkid r (HTWIN:twin_state st1 st2 blkid),
    Ir.Memory.allocatable (Ir.Config.m st1) r =
    Ir.Memory.allocatable (Ir.Config.m st2) r.
Proof.
  intros.
  unfold Ir.Memory.allocatable.
  assert (HP:Permutation (r ++ Ir.Memory.alive_P_ranges (Ir.Config.m st1))
                         (r ++ Ir.Memory.alive_P_ranges (Ir.Config.m st2))).
  { apply Permutation_app.
    { apply Permutation_refl. }
    { admit. }
  }
  apply disjoint_ranges_Permutation.
  assumption.
Admitted.


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

Lemma twin_execution_unidir:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
         (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (* Input state st1 and st2 are twin-state. *)
         (HTWIN:twin_state st1 st2 blkid)
         (* Current instruction wouldn't do memory access
            from a guessed pointer. *)
         (HNOGUESSEDACCESS:~ memaccess_from_possibly_guessedptr md st1)
         (* Current instruction never observes block id blkid. *)
         (HNOTOBSERVE: ~observes_block md st1 blkid),
    (* one way dir *)
    forall sr1 (HSTEP1:Ir.SmallStep.inst_step md st1 sr1),
          exists sr2, Ir.SmallStep.inst_step md st2 sr2 /\
                      twin_sresult sr1 sr2 blkid.
Proof.
  intros.
  inv HSTEP1.
  { unfold Ir.SmallStep.inst_det_step in HNEXT.
    remember (Ir.Config.cur_inst md st1) as oi1.
    destruct oi1 as [i1 | ].
    { erewrite twin_state_cur_inst_eq in Heqoi1; try (apply HTWIN; fail).
      destruct i1; inv HNEXT.
      { (* binop *)
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          reflexivity. }
        { erewrite twin_state_get_val_eq with (st1 := st1);
            try (apply HTWIN; fail).
          erewrite twin_state_get_val_eq with (st1 := st1);
            try (apply HTWIN; fail).
          eapply ts_success.
          { reflexivity. }
          { reflexivity. }
          { thats_it. }
        }
      }
      { (* psub *)
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          reflexivity. }
        { erewrite <- twin_state_get_val_eq with (st1 := st1) (st2 := st2);
            try (apply HTWIN; fail).
          erewrite <- twin_state_get_val_eq with (st1 := st1) (st2 := st2);
            try (apply HTWIN; fail).
          eapply ts_success.
          { reflexivity. }
          { reflexivity. }
          { destruct t; try thats_it.
            destruct (Ir.Config.get_val st1 o) eqn:Hop1; try thats_it.
            destruct v; try thats_it.
            destruct (Ir.Config.get_val st1 o0) eqn:Hop2; try thats_it.
            destruct v; try thats_it.
            destruct p; destruct p0.
            { unfold Ir.SmallStep.psub. thats_it. }
            { destruct (b =? blkid) eqn:HBLKID.
              { (* observed. *)
                rewrite PeanoNat.Nat.eqb_eq in HBLKID.
                subst b.
                assert (Heqoi2 := Heqoi1).
                rewrite twin_state_cur_inst_eq with (st2 := st1) (blkid := blkid)
                  in Heqoi2 by (apply twin_state_sym in HTWIN; assumption).
                assert (observes_block md st1 blkid).
                { eapply ob_by_psub_l.
                  { rewrite Heqoi2. reflexivity. }
                  { rewrite Hop1. reflexivity. }
                  { rewrite Hop2. reflexivity. }
                }                
                congruence.
              }
              { unfold Ir.SmallStep.psub.
                rewrite PeanoNat.Nat.eqb_neq in HBLKID.
                rewrite twin_state_p2N_eq with (st2 := st2) (blkid := blkid);
                  try assumption.
                thats_it.
              }
            }
            { destruct (b =? blkid) eqn:HBLKID.
              { (* observed. *)
                rewrite PeanoNat.Nat.eqb_eq in HBLKID.
                subst b.
                assert (Heqoi2 := Heqoi1).
                rewrite twin_state_cur_inst_eq with (st2 := st1) (blkid := blkid)
                  in Heqoi2 by (apply twin_state_sym in HTWIN; assumption).
                assert (observes_block md st1 blkid).
                { eapply ob_by_psub_r.
                  { rewrite Heqoi2. reflexivity. }
                  { rewrite Hop2. reflexivity. }
                  { rewrite Hop1. reflexivity. }
                }
                congruence.
              }
              { unfold Ir.SmallStep.psub.
                rewrite PeanoNat.Nat.eqb_neq in HBLKID.
                rewrite twin_state_p2N_eq with (st2 := st2) (blkid := blkid);
                  try assumption.
                thats_it.
              }
            }
            { unfold Ir.SmallStep.psub. thats_it. }
        }
      }
    }
    { (* gep *)
      eexists. split.
      { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite <- Heqoi1.
        reflexivity. }
      { erewrite <- twin_state_get_val_eq with (st2 := st2);
          try (apply HTWIN; fail).
        erewrite <- twin_state_get_val_eq with (st2 := st2);
          try (apply HTWIN; fail).
        eapply ts_success.
        { reflexivity. }
        { reflexivity. }
        { destruct t; try thats_it.
          destruct (Ir.Config.get_val st1 o) eqn:Hop1; try thats_it.
          destruct v; try thats_it.
          destruct (Ir.Config.get_val st1 o0) eqn:Hop2; try thats_it.
          destruct v; try thats_it.
          destruct p.
          { erewrite twin_state_gep_eq; try eassumption.
            thats_it.
          }
          { unfold Ir.SmallStep.gep. thats_it. }
        }
      }
    }
    { (* load *)
      destruct (Ir.Config.get_val st1 o) eqn:Hop11.
      destruct v.
      { dup Hop11.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop0;
          try apply HTWIN.
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          rewrite Hop0.
          reflexivity. }
        { inv H0. eapply ts_success. reflexivity. reflexivity.
          thats_it. }
      }
      destruct p eqn:HP.
      { (* logical ptr: okay *)
        destruct (Ir.deref (Ir.Config.m st1) (Ir.plog b n) (Ir.ty_bytesz t))
                 eqn:HDEREF.
        {
          dup HDEREF.
          erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
          rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF0;
            try assumption.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1.
            rewrite Hop11.
            rewrite HDEREF0. reflexivity. }
          { inv H0. eapply ts_success.
            {reflexivity. } { reflexivity. }
            { erewrite twin_state_load_val_eq. thats_it.
              eassumption. }
          }
        }
        { inv H0.
          dup HDEREF.
          erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
          rewrite twin_state_deref_eq with (st2 := st2) (blkid := blkid) in HDEREF0;
            try assumption.
          eexists.
          split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1.
            rewrite Hop11.
            rewrite HDEREF0. reflexivity. }
          { eapply ts_goes_wrong; reflexivity. }
        }
      }
      { (* physical ptr: no *)
        assert (memaccess_from_possibly_guessedptr md st1).
        { eapply gp_load.
          symmetry in Hop11. eapply Hop11.
          econstructor. reflexivity.
          rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                                 (blkid := blkid) in Heqoi1;
            try assumption.
          rewrite Heqoi1. reflexivity.
        }
        congruence.
      }
      { (* ty is problematic *)
        inv H0.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
          try apply HTWIN.
        eexists . split. 
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          rewrite Hop11. reflexivity. }
        { eapply ts_success; try reflexivity. thats_it. }
      }
      { inv H0.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
          try apply HTWIN.
        eexists. split.
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          rewrite Hop11. reflexivity. }
        { eapply ts_success; try reflexivity. thats_it. }
      }
    }
    { (* store *)
      destruct (Ir.Config.get_val st1 o) eqn:Hop11;
      destruct (Ir.Config.get_val st2 o) eqn:Hop21;
      destruct (Ir.Config.get_val st1 o0) eqn:Hop12;
      destruct (Ir.Config.get_val st2 o0) eqn:Hop22;
      try(erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN; congruence);
      try(erewrite twin_state_get_val_eq with (st2 := st2) in Hop12;
            try apply HTWIN; congruence).
      { destruct v eqn:HV; inv H0;
        try (erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN;
            rewrite Hop21 in Hop11; inv Hop11;
            eexists; split;
            [ apply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
              rewrite <- Heqoi1;
              rewrite Hop21; reflexivity
            | eapply ts_success;
              [ reflexivity
                | reflexivity
                | apply twin_state_incrpc; assumption ]
            ]).
        destruct (Ir.deref (Ir.Config.m st1) p (Ir.ty_bytesz t))
                 eqn:HDEREF; inv H1; destruct p.
        {
          dup HDEREF.
          erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
          rewrite Hop21 in Hop11. inv Hop11.
          rewrite twin_state_deref_eq with (st1 := st1) (st2 := st2)
                                           (blkid := blkid) in HDEREF0;
            try assumption.
          eexists.
          split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1.
            rewrite Hop21, Hop22.
            rewrite HDEREF0. reflexivity. }
          { eapply ts_success.
            { reflexivity. }
            { reflexivity. }
            { eapply twin_state_incrpc.
              erewrite twin_state_get_val_eq with (st2 := st2) in Hop12;
                try apply HTWIN.
              rewrite Hop12 in Hop22. inv Hop22.
              eapply twin_state_store_val; try eassumption.
              { apply ty_bytesz_pos. }
            }
          }
        }
        { (* ptr is physical pointer. *)
          assert (memaccess_from_possibly_guessedptr md st1).
          { econstructor. rewrite Hop11. reflexivity.
            econstructor.  reflexivity.
            rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
              in Heqoi1; try assumption.
            rewrite <- Heqoi1. reflexivity.
          }
          congruence.
        }
        { (* UB *)
          dup HDEREF.
          rewrite twin_state_deref_eq with (st1 := st1) (st2 := st2)
                                           (blkid := blkid) in HDEREF0;
            try assumption.
          erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
          dup Hop21.
          rewrite Hop11 in Hop21. inv Hop21.
          eexists.
          split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1.
            rewrite Hop0. rewrite Hop22.
            rewrite HDEREF0. reflexivity. }
          { constructor; reflexivity. }
        }
        { (* ptr is physical pointer. *)
          assert (memaccess_from_possibly_guessedptr md st1).
          { econstructor. rewrite Hop11. reflexivity.
            econstructor.  reflexivity.
            rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
              in Heqoi1; try assumption.
            rewrite <- Heqoi1. reflexivity.
          }
          congruence.
        }
      }
      { (* Hop22, Hop12 is none.*)
        dup Hop11. dup Hop21.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
        rewrite Hop11 in Hop1. inv Hop1.
        destruct v0.
        { inv H0.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1. rewrite Hop21. reflexivity.
          }
          { eapply ts_success.
            reflexivity. reflexivity.
            apply twin_state_incrpc. assumption. }
        }
        { inv H0.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1. rewrite Hop21. rewrite Hop22. reflexivity.
          }
          { eapply ts_success.
            reflexivity. reflexivity.
            apply twin_state_incrpc. assumption. }
        }
        { inv H0.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1. rewrite Hop21. reflexivity.
          }
          { eapply ts_success.
            reflexivity. reflexivity.
            apply twin_state_incrpc. assumption. }
        }
      }
      { (* Hop11, Hop21 is none.*)
        dup Hop12. dup Hop22.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop12;
            try apply HTWIN.
        rewrite Hop12 in Hop1. inv Hop1. inv H0.
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1. rewrite Hop21. reflexivity.
        }
        { eapply ts_success.
          reflexivity. reflexivity.
          apply twin_state_incrpc. assumption. }
      }
      { (* all ops are none.*)
        inv H0.
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1. rewrite Hop21. reflexivity.
        }
        { eapply ts_success.
          reflexivity. reflexivity.
          apply twin_state_incrpc. assumption. }
      }
    }
    { (* free *)
      (* instruction Heqoi1 *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.


      destruct (Ir.Config.get_val st1 o) eqn:Hop1.
      { remember (Ir.Config.get_val st2 o) as op2 eqn:Hop2.
        coalesce_op Hop1 Hop2 st2 HTWIN.
        destruct v.
        { (* free (int) -_-; *)
          inv H0.
          eexists . split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2.
            rewrite H. reflexivity. }
          { eapply ts_goes_wrong; reflexivity. }
        }
        { (* free (ptr) *)
          destruct p.
          { (* free(log) *)
            assert (HBIG:(exists m1 m2,
        Some m1 = (Ir.SmallStep.free (Ir.plog b n) (Ir.Config.m st1)) /\
        Some m2 = (Ir.SmallStep.free (Ir.plog b n) (Ir.Config.m st2)) /\
        twin_state (Ir.Config.update_m st1 m1)
                   (Ir.Config.update_m st2 m2)
                   blkid) \/
        (None = Ir.SmallStep.free (Ir.plog b n) (Ir.Config.m st1) /\
         None = Ir.SmallStep.free (Ir.plog b n) (Ir.Config.m st2))).
            { eapply twin_state_free; eassumption. }
            destruct HBIG.
            { destruct H1 as [m1 [m2 [H1 [H2 H3]]]].
              rewrite <- H1 in H0. inv H0.
              eexists.
              split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite H.
                rewrite <- H2. reflexivity. }
              { eapply ts_success. reflexivity. reflexivity.
                eapply twin_state_incrpc. eassumption. }
            }
            { destruct H1. rewrite <- H1 in H0.
              inv H0.
              eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite H. rewrite <- H2. reflexivity. }
              { eapply ts_goes_wrong; reflexivity. }
            }
          }
          { (* free(phy) *)
            assert (memaccess_from_possibly_guessedptr md st1).
            { eapply gp_free. symmetry in Hop1. eassumption.
              econstructor. reflexivity.
              eassumption.
            }
            congruence.
          }
        }
        { (* free (int) -_-; *)
          inv H0.
          eexists . split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2.
            rewrite H. reflexivity. }
          { eapply ts_goes_wrong; reflexivity. }
        }
      }
      { (* goes wrong *)
        inv H0.
        eexists. split.
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi2.
          remember (Ir.Config.get_val st2 o) as op2 eqn:Hop2.
          coalesce_op Hop1 Hop2 st2 HTWIN.
          reflexivity. }
        { eapply ts_goes_wrong; reflexivity. }
      }
    }
    { (* bit cast *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      eexists. split.
      { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite <- Heqoi2. reflexivity. }
      { assert (HOP:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
        { eapply twin_state_get_val_eq. eassumption. }
        rewrite HOP.
        eapply ts_success. reflexivity. reflexivity.
        thats_it. }
    }
    { (* ptrtoint *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      eexists. split.
      { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite <- Heqoi2. reflexivity. }
      { assert (HOP:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
        { eapply twin_state_get_val_eq. eassumption. }
        rewrite HOP.
        destruct t; try (eapply ts_success; try reflexivity; thats_it).
        destruct (Ir.Config.get_val st2 o) eqn:HOPVAL;
          try (eapply ts_success; try reflexivity; thats_it).
        { destruct v; try (eapply ts_success; try reflexivity; thats_it).
          destruct p.
          { (* p shouldn't be log (blkid, ..) *)
            destruct (b =? blkid) eqn:HBLKID.
            { rewrite PeanoNat.Nat.eqb_eq in HBLKID.
              assert (observes_block md st1 blkid).
              { eapply ob_by_ptrtoint.
                eassumption. rewrite HOP. subst. reflexivity. }
              congruence.
            }
            { rewrite PeanoNat.Nat.eqb_neq in HBLKID.
              dup HTWIN.
              decompose_HTWIN HTWIN b.
              destruct HTWIN5'. exploit H0. assumption.
              intros HH. clear H H0.
              unfold Ir.SmallStep.p2N.
              unfold Ir.log_to_phy.
              rewrite HH.
              eapply ts_success; try reflexivity.
              eapply twin_state_update_reg_and_incrpc.
              eassumption.
            }
          }
          { (* p is phy is okay. *)
            unfold Ir.SmallStep.p2N.
            eapply ts_success; try reflexivity. thats_it.
          }
        }
      }
    }
    { (* inttoptr *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      eexists. split.
      { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite <- Heqoi2. reflexivity. }
      { assert (HOP:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
        { eapply twin_state_get_val_eq. eassumption. }
        rewrite HOP.
        eapply ts_success. reflexivity. reflexivity.
        thats_it. }
    }
    { (* ievent *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      assert (HOP:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
      { eapply twin_state_get_val_eq. eassumption. }
      destruct (Ir.Config.get_val st1 o) eqn:HOP1.
      { destruct v.
        { inv H0.
          eexists. split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2. rewrite <- HOP.
            reflexivity. }
          { eapply ts_success; try reflexivity.
            eapply twin_state_incrpc. assumption. }
        }
        { inv H0.
          eexists. split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2. rewrite <- HOP.
            reflexivity. }
          { eapply ts_goes_wrong; try reflexivity. }
        }
        { inv H0.
          eexists. split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2. rewrite <- HOP.
            reflexivity. }
          { eapply ts_goes_wrong; try reflexivity. }
        }
      }
      { inv H0.
        eexists. split.
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi2. rewrite <- HOP.
          reflexivity. }
        { eapply ts_goes_wrong; try reflexivity. }
      }
    }
    { (* icmp ule *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      assert (HOPEQ1:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
      { eapply twin_state_get_val_eq. eassumption. }
      assert (HOPEQ2:Ir.Config.get_val st1 o0 = Ir.Config.get_val st2 o0).
      { eapply twin_state_get_val_eq. eassumption. }
      destruct (Ir.Config.get_val st1 o) eqn:Hop11.
      { destruct v.
        { destruct (Ir.Config.get_val st1 o0) eqn:Hop12.
          { destruct v; inv H0.
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
          }
          { inv H0.
            eexists. split.
            { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
            { eapply ts_success; try reflexivity. thats_it. }
          }
        }
        { destruct (Ir.Config.get_val st1 o0) eqn:Hop12.
          { destruct v.
            { inv H0. eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { (* okay, the important case. *)
              unfold Ir.SmallStep.icmp_eq_ptr in H0.
              erewrite twin_state_icmp_eq_ptr_nondet_cond_eq in H0; try eassumption.
              destruct p; destruct p0.
              { (* log, log *)
                destruct (b =? b0) eqn:HBB0.
                { inv H0.
                  eexists. split.
                  { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                    rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                    unfold Ir.SmallStep.icmp_eq_ptr. rewrite HBB0. reflexivity. }
                  { eapply ts_success; try reflexivity. thats_it. }
                }
                { des_ifs.
                  eexists. split.
                  { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                    rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                    unfold Ir.SmallStep.icmp_eq_ptr. rewrite HBB0.
                    rewrite Heq0. reflexivity. }
                  { eapply ts_success; try reflexivity. thats_it. }
                }
              }
              { (* log, phy *)
                assert (b <> blkid).
                { intros HH. assert (observes_block md st1 blkid).
                  { eapply ob_by_iicmpeq_l. rewrite Heqoi1. reflexivity.
                    rewrite Hop11. subst. reflexivity.
                    rewrite Hop12. reflexivity. }
                  congruence. }
                erewrite twin_state_p2N_eq in H0; try eassumption.
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
              { (* phy. log *)
                assert (b <> blkid).
                { intros HH. assert (observes_block md st1 blkid).
                  { eapply ob_by_iicmpeq_r. rewrite Heqoi1. reflexivity.
                    rewrite Hop12. subst. reflexivity.
                    rewrite Hop11. reflexivity. }
                  congruence. }
                erewrite twin_state_p2N_eq in H0; try eassumption.
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
              { (* phy phy *)
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
            }
            { inv H0.
              eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
          }
          { inv H0.
            eexists. split.
            { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
            { eapply ts_success; try reflexivity. thats_it. }
          }
        }
        { inv H0.
          eexists. split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2. rewrite <- HOPEQ1. reflexivity. }
          { eapply ts_success; try reflexivity. thats_it. }
        }
      }
      { inv H0.
        eexists. split.
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi2. rewrite <- HOPEQ1. reflexivity. }
        { eapply ts_success; try reflexivity. thats_it. }
      }
    }
    { (* icmp ule *)
      assert (Heqoi2 := Heqoi1).
      rewrite <- twin_state_cur_inst_eq with (st1 := st1)
                                             (blkid := blkid) in Heqoi1;
        try assumption.
      assert (HOPEQ1:Ir.Config.get_val st1 o = Ir.Config.get_val st2 o).
      { eapply twin_state_get_val_eq. eassumption. }
      assert (HOPEQ2:Ir.Config.get_val st1 o0 = Ir.Config.get_val st2 o0).
      { eapply twin_state_get_val_eq. eassumption. }
      destruct (Ir.Config.get_val st1 o) eqn:Hop11.
      { destruct v.
        { destruct (Ir.Config.get_val st1 o0) eqn:Hop12.
          { destruct v; inv H0.
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
          }
          { inv H0.
            eexists. split.
            { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
            { eapply ts_success; try reflexivity. thats_it. }
          }
        }
        { destruct (Ir.Config.get_val st1 o0) eqn:Hop12.
          { destruct v.
            { inv H0. eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
            { (* okay, the important case. *)
              unfold Ir.SmallStep.icmp_ule_ptr in H0.
              erewrite twin_state_icmp_ule_ptr_nondet_cond_eq in H0; try eassumption.
              destruct p; destruct p0.
              { (* log, log *)
                des_ifs.
                { eexists. split.
                  { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                    rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                    unfold Ir.SmallStep.icmp_ule_ptr. rewrite Heq0. reflexivity. }
                  { eapply ts_success; try reflexivity.
                    dup HTWIN.
                    decompose_HTWIN HTWIN b.
                    destruct (b =? blkid) eqn:HBLKID.
                    { (* The twin block *)
                      rewrite PeanoNat.Nat.eqb_eq in HBLKID.
                      destruct HTWIN5'. clear H0. exploit H. congruence.
                      intros HH. decompose_mbs HH.  subst b. rewrite <- HH1.
                      thats_it. }
                    { (* not the twin block *)
                      rewrite PeanoNat.Nat.eqb_neq in HBLKID.
                      destruct HTWIN5'. clear H. exploit H0. congruence.
                      intros HH. rewrite <- HH. rewrite Heq.
                      thats_it. }
                  }
                }
                {
                  dup HTWIN.
                  decompose_HTWIN HTWIN b.
                  destruct (b =? blkid) eqn:HBLKID.
                  { (* The twin block *)
                    (*Memory.get b cnanot be None. *)
                    rewrite PeanoNat.Nat.eqb_eq in HBLKID.
                    destruct HTWIN5'. clear H0. exploit H. congruence.
                    intros HH. decompose_mbs HH.  subst b. congruence. }
                  { (* not the twin block *)
                      rewrite PeanoNat.Nat.eqb_neq in HBLKID.
                      destruct HTWIN5'. clear H. exploit H0. congruence.
                      intros HH.
                      eexists. split.
                      { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                        rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                        unfold Ir.SmallStep.icmp_ule_ptr. rewrite Heq0. reflexivity. }
                      { eapply ts_success; try reflexivity. rewrite <- HH.
                        rewrite Heq.
                        thats_it. }
                  }
                }
              }
              { (* log, phy *)
                assert (b <> blkid).
                { intros HH. assert (observes_block md st1 blkid).
                  { eapply ob_by_iicmpule_l. rewrite Heqoi1. reflexivity.
                    rewrite Hop11. subst. reflexivity.
                    rewrite Hop12. reflexivity. }
                  congruence. }
                erewrite twin_state_p2N_eq in H0; try eassumption.
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
              { (* phy. log *)
                assert (b <> blkid).
                { intros HH. assert (observes_block md st1 blkid).
                  { eapply ob_by_iicmpule_r. rewrite Heqoi1. reflexivity.
                    rewrite Hop12. subst. reflexivity.
                    rewrite Hop11. reflexivity. }
                  congruence. }
                erewrite twin_state_p2N_eq in H0; try eassumption.
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
              { (* phy phy *)
                inv H0.
                eexists. split.
                { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                  rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2.
                  unfold Ir.SmallStep.icmp_ule_ptr. reflexivity. }
                { eapply ts_success; try reflexivity. thats_it. }
              }
            }
            { inv H0.
              eexists. split.
              { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
                rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
              { eapply ts_success; try reflexivity. thats_it. }
            }
          }
          { inv H0.
            eexists. split.
            { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite <- Heqoi2. rewrite <- HOPEQ1, <- HOPEQ2. reflexivity. }
            { eapply ts_success; try reflexivity. thats_it. }
          }
        }
        { inv H0.
          eexists. split.
          { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi2. rewrite <- HOPEQ1. reflexivity. }
          { eapply ts_success; try reflexivity. thats_it. }
        }
      }
      { inv H0.
        eexists. split.
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi2. rewrite <- HOPEQ1. reflexivity. }
        { eapply ts_success; try reflexivity. thats_it. }
      }
    }
  }
  { inv HNEXT.
    assert (Heqoi2 := Heqoi1).
    rewrite twin_state_cur_inst_eq with (st2 := st2)
                                           (blkid := blkid) in Heqoi2.
    { eexists. split.
      { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite <- Heqoi2. reflexivity. }
      { eapply ts_goes_wrong; try reflexivity. }
    }
    { eassumption. }
  }
}
  { (* malloc null *)
    rename HCUR into Heqoi1.
    assert (Heqoi2 := Heqoi1).
    rewrite twin_state_cur_inst_eq with (st2 := st2)
                                           (blkid := blkid) in Heqoi2.
    { eexists. split.
      { eapply Ir.SmallStep.s_malloc_null. eassumption. reflexivity. }
      { eapply ts_success; try reflexivity. thats_it. }
    }
    { eassumption. }
  }
  { (* malloc oom. *)
    rename HCUR into Heqoi1.
    assert (Heqoi2 := Heqoi1).
    rewrite twin_state_cur_inst_eq with (st2 := st2)
                                           (blkid := blkid) in Heqoi2;
      try assumption.
    { eexists. split.
      { eapply Ir.SmallStep.s_malloc_oom.
        { eassumption. }
        { reflexivity. }
        { erewrite twin_state_get_val_eq. eassumption.
          eapply twin_state_sym. eassumption. }
        { 
          intros HE.
          apply HNOSPACE.
          destruct HE.
          rewrite twin_state_allocatable_eq with (st2 := st1) (blkid := blkid) in H.
          exists x. assumption.
          apply twin_state_sym. assumption.
        }
      }
      { eapply ts_oom;try reflexivity. }
    }
  }
  { (* malloc succeed *)
    rename HCUR into Heqoi1.
    assert (Heqoi2 := Heqoi1).
    rewrite twin_state_cur_inst_eq with (st2 := st2)
                                           (blkid := blkid) in Heqoi2.
    { eexists. split.
      { eapply Ir.SmallStep.s_malloc.
        { eassumption. }
        { reflexivity. }
        { erewrite twin_state_get_val_eq. eassumption.
          eapply twin_state_sym. eassumption. }
        { eassumption. }
        { reflexivity. }
        { eassumption. }
        { rewrite <- twin_state_allocatable_eq with (st1 := st1) (blkid := blkid);
          assumption. }
        { reflexivity. }
      }
      { eapply ts_success; try reflexivity.
        unfold Ir.Memory.new in HNEW.
        inv HNEW.
        decompose_HTWIN HTWIN 0.
        rewrite HTWIN2.
        rewrite HTWIN3.
        rewrite HTWIN4.
        split.
        { rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          eapply eq_wom_update_m.

          eapply eq_wom_update_reg_and_incrpc. assumption.
        }
        split.
        { rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          simpl. reflexivity. }
        split.
        { rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          simpl. reflexivity. }
        split.
        { rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          rewrite Ir.Reordering.update_reg_and_incrpc_update_m.
          rewrite Ir.Reordering.m_update_m.
          simpl. reflexivity. }
        rewrite Ir.Reordering.m_update_reg_and_incrpc.
        rewrite Ir.Reordering.m_update_reg_and_incrpc.
        rewrite Ir.Reordering.m_update_m.
        rewrite Ir.Reordering.m_update_m.
        simpl.
        split.
        { intros HH. destruct (HTWIN5 bid').
          exploit H. congruence. intros HH'.
          decompose_mbs' HH'.
          destruct (Ir.Memory.fresh_bid (Ir.Config.m st2) =? blkid) eqn:HBLKID.
          { (* impossible *)
            inv HWF2.
            inv wf_m.
            rewrite PeanoNat.Nat.eqb_eq in HBLKID.
            assert (blkid < Ir.Memory.fresh_bid (Ir.Config.m st2)).
            { 
              apply forallb_In with (i := blkid) in wf_newid.
              rewrite PeanoNat.Nat.ltb_lt in wf_newid. assumption.
              apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st2))
                in HH1'.
              apply list_keys_In in HH1'.
              assumption.
              reflexivity.
            }
            rewrite HBLKID in H1.
            omega.
          }
          { unfold Ir.Memory.get.
            simpl. rewrite HBLKID.
            unfold Ir.Memory.get in HH0', HH1'.
            eexists. eexists.
            split. rewrite <- HH0'. reflexivity.
            split. rewrite <- HH1'. reflexivity.
            repeat (split; try congruence).
          }
        }
        {
          intros.
          clear HTWIN5'.
          assert (HTWIN5' := HTWIN5 bid').
          destruct HTWIN5'. exploit H0. assumption. intros HH.
          clear H0 H.
          unfold Ir.Memory.get.
          simpl.
          destruct (Ir.Memory.fresh_bid (Ir.Config.m st2) =? bid').
          { simpl. reflexivity. }
          { unfold Ir.Memory.get in HH. assumption. }
        }
      }
    }
    assumption.
  }

Theorem twin_exe:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
    (* If block blkid is never observed.. *)
    (HNEVER_OBSERVED: forall (st:Ir.Config.t), ~ observes_block md st blkid),

    forall (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
           (* Input state st1 and st2 are twin-state. *)
           (HTWIN:twin_state st1 st2 blkid),
      (* Bisimulation. *)
      (forall sr1 (HSTEP1:Ir.SmallStep.inst_step md st1 sr1),
          exists sr2, Ir.SmallStep.inst_step md st2 sr2 /\
                      twin_sresult sr1 sr2 blkid) /\
      (forall sr2 (HSTEP1:Ir.SmallStep.inst_step md st2 sr2),
          exists sr1, Ir.SmallStep.inst_step md st1 sr1 /\
                      twin_sresult sr1 sr2 blkid).
Proof.
  intros.

  
Qed.

Definition

End Ir.
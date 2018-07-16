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
        (HINST: Some (Ir.Inst.istore valty opval opptr) =
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
  unfold LoadStore.Ir.log_to_phy.
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
    LoadStore.Ir.deref (Ir.Config.m st1) (Ir.plog l ofs) n =
    LoadStore.Ir.deref (Ir.Config.m st2) (Ir.plog l ofs) n.
Proof.
  intros.
  unfold LoadStore.Ir.deref.
  unfold LoadStore.Ir.get_deref.
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


Lemma twin_state_load_bytes_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid) l ofs thety,
    LoadStore.Ir.load_bytes (Ir.Config.m st1) (Ir.plog l ofs) thety =
    LoadStore.Ir.load_bytes (Ir.Config.m st2) (Ir.plog l ofs) thety.
Proof.
  intros.
  unfold LoadStore.Ir.load_bytes.
    destruct (LoadStore.Ir.get_deref
                (Ir.Config.m st1) (Ir.plog l ofs) thety)
    eqn:HGD1;
    destruct (LoadStore.Ir.get_deref
                (Ir.Config.m st2) (Ir.plog l ofs) thety)
             eqn:HGD2; try reflexivity.
  { unfold LoadStore.Ir.get_deref in HGD1, HGD2.
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
  { unfold LoadStore.Ir.get_deref in HGD1, HGD2.
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
  { unfold LoadStore.Ir.get_deref in HGD1, HGD2.
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
    LoadStore.Ir.load_val (Ir.Config.m st1) (Ir.plog l ofs) thety =
    LoadStore.Ir.load_val (Ir.Config.m st2) (Ir.plog l ofs) thety.
Proof.
  intros.
  unfold LoadStore.Ir.load_val.
  destruct thety.
  { erewrite twin_state_load_bytes_eq. reflexivity.
    eassumption. }
  { erewrite twin_state_load_bytes_eq. reflexivity.
    eassumption. }
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

Lemma twin_execution_unidir:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
         (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
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
        destruct (LoadStore.Ir.deref (Ir.Config.m st1) (Ir.plog b n) (Ir.ty_bytesz t))
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

      
  
Qed.

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
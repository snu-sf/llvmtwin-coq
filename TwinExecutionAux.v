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
Require Import WellTyped.
Require Import LoadStore.
Require Import SmallStep.
Require Import TwinExecution.

Module Ir.

Import TwinExecution.
Import Ir.

Lemma twin_state_sym:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid),
    twin_state st2 st1 blkid.
Proof.
  intros.
  inv HTWIN.
  split.
  { apply Ir.Config.eq_wom_sym. assumption. }
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

Lemma twin_state_allocatable_eq:
  forall st1 st2 blkid r md
         (HTWIN:twin_state st1 st2 blkid)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2),
    Ir.Memory.allocatable (Ir.Config.m st1) r =
    Ir.Memory.allocatable (Ir.Config.m st2) r.
Proof.
  intros.
  unfold Ir.Memory.allocatable.
  assert (HP:Permutation (r ++ Ir.Memory.alive_P_ranges (Ir.Config.m st1))
                         (r ++ Ir.Memory.alive_P_ranges (Ir.Config.m st2))).
  { apply Permutation_app.
    { apply Permutation_refl. }
    { unfold Ir.Memory.alive_P_ranges.
      unfold Ir.Memory.alive_blocks.
      remember (Ir.Memory.blocks (Ir.Config.m st1)) as mbs1.
      remember (Ir.Memory.blocks (Ir.Config.m st2)) as mbs2.
      assert (HNODUP1:List.NoDup mbs1).
      { inv HWF1. inv wf_m.
        apply list_keys_NoDup.
        apply wf_uniqueid. }
      assert (HNODUPK1:List.NoDup (list_keys mbs1)).
      { inv HWF1. inv wf_m. assumption. }
      assert (HNODUP2:List.NoDup mbs2).
      { inv HWF2. inv wf_m.
        apply list_keys_NoDup.
        apply wf_uniqueid. }
      assert (HNODUPK2:List.NoDup (list_keys mbs2)).
      { inv HWF2. inv wf_m. assumption. }
      destruct (list_find_key mbs1 blkid) eqn:HAS_BLKID;
      destruct (list_find_key mbs2 blkid) eqn:HAS_BLKID2.
      { (* okay, Permutation mbs1 mbs2 should hold. *)
        assert (Permutation mbs1 mbs2).
        { apply NoDup_Permutation;try eauto.
          { intros.
            inv HTWIN.
            destruct H0. destruct H1. destruct H2.
            assert (H3' := H3 (fst x)). clear H3.
            destruct H3'. clear H3.
            split.
            { intros HH.
              assert (HNOX: fst x <> blkid).
              { eapply list_find_key_In_none.
                eapply HAS_BLKID. assumption. }
              apply H4 in HNOX. clear H4.
              destruct (Ir.Memory.get (Ir.Config.m st1) (fst x)) eqn:HGET1.
              { symmetry in HGET1.
                apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HGET1;
                  try reflexivity.
                apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st2)) in HNOX;
                  try reflexivity.
                destruct x.
                simpl in *.
                assert (t = t0).
                { eapply list_find_key_NoDup_In2.
                  eapply HGET1. eapply HH. assumption. }
                subst t. assumption.
              }
              { assert (~ List.In x (Ir.Memory.blocks (Ir.Config.m st1))).
                { destruct x. eapply Ir.Memory.get_not_In.
                  symmetry in HGET1. eapply HGET1. reflexivity. }
                congruence.
              }
            }
            { intros HH.
              assert (HNOX: fst x <> blkid).
              { eapply list_find_key_In_none.
                eapply HAS_BLKID2. assumption. }
              apply H4 in HNOX. clear H4.
              destruct (Ir.Memory.get (Ir.Config.m st2) (fst x)) eqn:HGET2.
              { symmetry in HGET2.
                apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st2)) in HGET2;
                  try reflexivity.
                symmetry in HNOX.
                apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HNOX;
                  try reflexivity.
                destruct x.
                simpl in *.
                assert (t = t0).
                { eapply list_find_key_NoDup_In2.
                  eapply HGET2. eapply HH. assumption. }
                subst t. assumption.
              }
              { assert (~ List.In x (Ir.Memory.blocks (Ir.Config.m st2))).
                { destruct x. eapply Ir.Memory.get_not_In.
                  symmetry in HGET2. eapply HGET2. reflexivity. }
                congruence.
              }
            }
          }
        }
        eapply concat_map_Permutation.
        eapply filter_Permutation.
        assumption.
      }
      { (* cannot happen *)
        inv HTWIN.
        destruct H0. destruct H1. destruct H2.
        assert (H3' := H3 blkid). clear H3.
        destruct H3'. clear H4. exploit H3.
        reflexivity. intros HH. clear H3.
        destruct HH. destruct H3. destruct H3. destruct H4.
        unfold Ir.Memory.get in H3, H4.
        rewrite HAS_BLKID in H3. congruence.
      }
      { (* cannot happen *)
        inv HTWIN.
        destruct H0. destruct H1. destruct H2.
        assert (H3' := H3 blkid). clear H3.
        destruct H3'. clear H4. exploit H3.
        reflexivity. intros HH. clear H3.
        destruct HH. destruct H3. destruct H3. destruct H4.
        unfold Ir.Memory.get in H3, H4.
        rewrite HAS_BLKID2 in H4. congruence.
      }
      { inv HTWIN.
        destruct H0. destruct H1. destruct H2.
        assert (H3' := H3 blkid).
        destruct H3'. clear H5. exploit H4.
        reflexivity. intros HH. clear H4.
        destruct HH. destruct H4. destruct H4. destruct H5.
        dup H4. dup H5.

        remember (Ir.Memory.blocks (Ir.Config.m st1)) as mbs1.
        remember (Ir.Memory.blocks (Ir.Config.m st2)) as mbs2.
        eapply Ir.Memory.get_In with (blks := mbs1) in H7.
        eapply Ir.Memory.get_In with (blks := mbs2) in H8.
        apply List.In_split in H7.
        apply List.In_split in H8.
        destruct H7 as [mbs11 [mbs12 HMBS1]].
        destruct H8 as [mbs21 [mbs22 HMBS2]].
        (* show that to_front has (blkd, _) at the front *)
        assert (HFRONT1: to_front mbs1 blkid = (blkid, x)::mbs11 ++ mbs12).
        { eapply to_front_spec. assumption. assumption. }
        assert (HFRONT2: to_front mbs2 blkid = (blkid, x0)::mbs21 ++ mbs22).
        { eapply to_front_spec. assumption. assumption. }

        (* Let's show that mbs11+mbs12 is permutation of mbs21++mbs22. *)
        (* to show this, we have to show that mbs11, mbs12, mbs21, ms22 does not
           have blkid. *)
        assert (HNOTIN1:~List.In blkid (list_keys (mbs11++mbs12))).
        { rewrite HMBS1 in HNODUPK1.
          rewrite list_keys_app in HNODUPK1.
          simpl in HNODUPK1.
          rewrite list_keys_app.
          apply List.NoDup_remove_2 in HNODUPK1.
          assumption. }
        assert (HNOTIN2:~List.In blkid (list_keys (mbs21++mbs22))).
        { rewrite HMBS2 in HNODUPK2.
          rewrite list_keys_app in HNODUPK2.
          simpl in HNODUPK2.
          rewrite list_keys_app.
          apply List.NoDup_remove_2 in HNODUPK2.
          assumption. }
        remember (mbs11++mbs12) as mbs1'.
        remember (mbs21++mbs22) as mbs2'.
        assert (HNODUP1':List.NoDup mbs1').
        { rewrite Heqmbs1'.
          eapply List.NoDup_remove_1.
          rewrite HMBS1 in HNODUP1. eassumption. }
        assert (HNODUP2':List.NoDup mbs2').
        { rewrite Heqmbs2'.
          eapply List.NoDup_remove_1.
          rewrite HMBS2 in HNODUP2. eassumption. }
        assert (HLSS1:lsubseq mbs1 mbs1').
        { rewrite Heqmbs1'. rewrite HMBS1.
          apply lsubseq_append. apply lsubseq_refl.
          constructor. apply lsubseq_refl.
        }
        assert (HLSS2:lsubseq mbs2 mbs2').
        { rewrite Heqmbs2'. rewrite HMBS2.
          apply lsubseq_append. apply lsubseq_refl.
          constructor. apply lsubseq_refl.
        }

        (* okay, Permutation mbs1' mbs2' should hold. *)
        assert (HPERM:Permutation mbs1' mbs2').
        { apply NoDup_Permutation; try eauto.
          { intros.
            assert (H3' := H3 (fst x1)). clear H3.
            destruct H3'. clear H3.
            split.
            { (* if x1 is in mbs1', it's in mbs2'. *)
              intros HH.
              (* x1's key can never be blkid. *)
              assert (HNOX: fst x1 <> blkid).
              { intros HH2. subst blkid. destruct x1.
                apply list_keys_In in HH. simpl in *. apply HNOTIN1. assumption. }
              dup HNOX.
              apply H7 in HNOX. clear H7.
              destruct (Ir.Memory.get (Ir.Config.m st1) (fst x1)) eqn:HGET1.
              { symmetry in HGET1.
                apply Ir.Memory.get_In with
                    (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HGET1;
                  try reflexivity.
                apply Ir.Memory.get_In with
                    (blks := Ir.Memory.blocks (Ir.Config.m st2)) in HNOX;
                  try reflexivity.
                destruct x1.
                simpl in *.
                assert (t = t0).
                { eapply list_find_key_NoDup_In2.
                  eapply HGET1.
                  eapply lsubseq_In.
                  eapply HH. rewrite Heqmbs1 in HLSS1. assumption.
                  rewrite Heqmbs1 in HNODUPK1. assumption. }
                subst t.
                rewrite Heqmbs2'.
                apply List.in_or_app.
                rewrite <- Heqmbs2 in HNOX.
                rewrite HMBS2 in HNOX.
                apply List.in_app_or in HNOX.
                destruct HNOX.
                { eauto. }
                { inv H3. { congruence. } { eauto. } }
              }
              { (* Memory.get (fst x1) is None..! *)
                assert (~ List.In x1 (Ir.Memory.blocks (Ir.Config.m st1))).
                { destruct x1. eapply Ir.Memory.get_not_In.
                  symmetry in HGET1. eapply HGET1. reflexivity. }
                apply lsubseq_NotIn with (l' := mbs1') in H3.
                { congruence. }
                { congruence. }
              }
            }
            { intros HH.
              assert (HNOX: fst x1 <> blkid).
              { intros HH2. subst blkid. destruct x1.
                apply list_keys_In in HH. simpl in *. apply HNOTIN2. assumption. }
              dup HNOX. apply H7 in HNOX. clear H7.
              destruct (Ir.Memory.get (Ir.Config.m st2) (fst x1)) eqn:HGET2.
              { symmetry in HGET2.
                apply Ir.Memory.get_In with
                    (blks := Ir.Memory.blocks (Ir.Config.m st2)) in HGET2;
                  try reflexivity.
                symmetry in HNOX.
                apply Ir.Memory.get_In with
                    (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HNOX;
                  try reflexivity.
                destruct x1.
                simpl in *.
                assert (t = t0).
                { eapply list_find_key_NoDup_In2.
                  eapply HGET2. eapply lsubseq_In.
                  eapply HH. rewrite <- Heqmbs2. assumption.
                  congruence. }
                subst t.
                rewrite Heqmbs1'.
                apply List.in_or_app.
                rewrite <- Heqmbs1 in HNOX.
                rewrite HMBS1 in HNOX.
                apply List.in_app_or in HNOX.
                destruct HNOX.
                { eauto. }
                { inv H3. { congruence. } { eauto. } }
              }
              { assert (~ List.In x1 (Ir.Memory.blocks (Ir.Config.m st2))).
                { destruct x1. eapply Ir.Memory.get_not_In.
                  symmetry in HGET2. eapply HGET2. reflexivity. }
                apply lsubseq_NotIn with (l' := mbs2') in H3.
                { congruence. }
                { congruence. }
              }
            }
          }
        }
        (* Okay, and now, for permutation of P of the twin block: *)
        assert (HPERM2': Permutation (Ir.MemBlock.P_ranges x) (Ir.MemBlock.P_ranges x0)).
        { destruct H6. destruct H7. destruct H8. destruct H9.
          unfold Ir.MemBlock.P_ranges. rewrite H8.
          eapply map_Permutation2.
          destruct H10. destruct H11. assumption. }

        (* yes, it's almost done!!*)
        (* now: show that filter mbs1' and filter mbs2' are pmerutation. *)
        remember (List.filter (fun xb => Ir.MemBlock.alive (snd xb)) mbs1') as mbs1f'.
        remember (List.filter (fun xb => Ir.MemBlock.alive (snd xb)) mbs2') as mbs2f'.
        assert (HPERM3:Permutation mbs1f' mbs2f').
        { rewrite Heqmbs1f', Heqmbs2f'. eapply filter_Permutation. assumption. }
        (* and, Permutation (map mbs1f') (map mbs2f'): *)
        remember (List.map (fun b => Ir.MemBlock.P_ranges (snd b)) mbs1f') as mbs1m'.
        remember (List.map (fun b => Ir.MemBlock.P_ranges (snd b)) mbs2f') as mbs2m'.
        assert (HPERM4:Permutation mbs1m' mbs2m').
        { rewrite Heqmbs1m', Heqmbs2m'. eapply map_Permutation. eassumption. }
        (* and, Permutation (concat ..) (concat ..): *)
        remember (List.concat mbs1m') as mbs1c'.
        remember (List.concat mbs2m') as mbs2c'.
        assert (HPERM5:Permutation mbs1c' mbs2c').
        { rewrite Heqmbs1c', Heqmbs2c'.

          eapply concat_Permutation2. assumption. }
        (* okay, now start with.. to_fronts. *)
        assert (HPERM6: Permutation
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                       (List.filter (fun xb => Ir.MemBlock.alive (snd xb))
                                    (to_front mbs1 blkid))))
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                       (List.filter (fun xb => Ir.MemBlock.alive (snd xb))
                                    (to_front mbs2 blkid))))).
        { rewrite HFRONT1. rewrite HFRONT2.
          simpl.
          assert (HALIVE: Ir.MemBlock.alive x = Ir.MemBlock.alive x0).
          { destruct H6. destruct H7.
            unfold Ir.MemBlock.alive. rewrite H7. congruence. }
          rewrite HALIVE in *.
          des_if.
          { simpl. eapply Permutation_app. assumption.
            { rewrite Heqmbs1c', Heqmbs2c' in HPERM5.
              rewrite Heqmbs1m', Heqmbs2m' in HPERM5.
              rewrite Heqmbs1f', Heqmbs2f' in HPERM5.
              assumption. }
          }
          { rewrite Heqmbs1c', Heqmbs2c' in HPERM5.
            rewrite Heqmbs1m', Heqmbs2m' in HPERM5.
            rewrite Heqmbs1f', Heqmbs2f' in HPERM5.
            assumption. }
        }
        assert (HPERM7:
                  Permutation
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                   (List.filter
                      (fun xb => Ir.MemBlock.alive (snd xb))
                      mbs1)))
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                   (List.filter
                      (fun xb => Ir.MemBlock.alive (snd xb))
                      (to_front mbs1 blkid))))).
        { apply concat_Permutation2. apply map_Permutation.
          apply filter_Permutation. apply to_front_Permutation. }
        assert (HPERM8:
                  Permutation
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                   (List.filter
                      (fun xb => Ir.MemBlock.alive (snd xb))
                      (to_front mbs2 blkid))))
             (List.concat
                (List.map (fun b => Ir.MemBlock.P_ranges (snd b))
                   (List.filter
                      (fun xb => Ir.MemBlock.alive (snd xb))
                      mbs2)))).
        { apply concat_Permutation2. apply map_Permutation.
          apply filter_Permutation.
          apply Permutation_sym. apply to_front_Permutation. }
        (* Now, a bunch of transitivity! *)
        eapply Permutation_trans.
        eapply HPERM7.
        eapply Permutation_trans.
        eapply HPERM6.
        eapply Permutation_trans.
        eapply HPERM8.
        (* and.. finally!*)
        eapply Permutation_refl.
        (* just a bunch of .. *)
        eassumption. eassumption.
      }
    }
  }
  apply disjoint_ranges_Permutation.
  assumption.
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

Lemma twin_state_cur_phi_eq:
  forall (md:Ir.IRModule.t) (st1 st2:Ir.Config.t) blkid
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.cur_phi md st1 = Ir.Config.cur_phi md st2.
Proof.
  intros.
  inv HTWIN.
  unfold Ir.Config.cur_phi.
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
      destruct H4'. assert (HDUMMY: blkid = blkid). reflexivity.
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
  forall st blkid ofs (n0:nat) isz mb
         (HDEREF:Ir.deref (Ir.Config.m st) (Ir.plog blkid ofs)
              (length (Ir.Byte.ofint (N.of_nat n0) isz)) = true)
         (HTYSZ:Ir.ty_bytesz (Ir.ity isz) = length (Ir.Byte.ofint (N.of_nat n0) isz))
         (HGET:Some mb = Ir.Memory.get (Ir.Config.m st) blkid)
         (HSZ:Ir.ty_bytesz (Ir.ity isz) >0)
         (HWF:Ir.Memory.wf
                (Ir.store_val (Ir.Config.m st) (Ir.plog blkid ofs)
                              (Ir.num n0) (Ir.ity isz))),
    Ir.Memory.wf
      (Ir.Memory.set (Ir.Config.m st) blkid
                     (Ir.MemBlock.set_bytes mb ofs (Ir.Byte.ofint (N.of_nat n0) isz))).
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
    unfold Ir.Byte.ofptr. unfold Ir.ty_bitsz.
    rewrite Ir.PTRSZ_def. reflexivity. }
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
  { apply Ir.Config.eq_wom_update_m. assumption. }
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
    repeat (rewrite Ir.Config.m_update_m).
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
          destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint (N.of_nat n0) n))
                   eqn:HWELLTYPED;
            destruct (snd (Ir.MemBlock.r mb2)) eqn:HR; simpl.
          { eexists. eexists.
            repeat (split; try eassumption). }
          { destruct ((ofs <=? Ir.MemBlock.n mb2) &&
                      (ofs + length (Ir.Byte.ofint (N.of_nat n0) n) <=? Ir.MemBlock.n mb2))
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
                (mb := mb1) (mb' := Ir.MemBlock.set_bytes mb1 ofs (Ir.Byte.ofint (N.of_nat n0) n));
                try eauto.
              rewrite Ir.Memory.get_set_id with (m := Ir.Config.m st2)
                (mb := mb2) (mb' := Ir.MemBlock.set_bytes mb2 ofs (Ir.Byte.ofint (N.of_nat n0) n));
                try eauto.
              { eexists. eexists.
                split. reflexivity.
                split. reflexivity.
                repeat (split; unfold Ir.MemBlock.set_bytes; simpl; try congruence).
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
          destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint (N.of_nat n0) n))
                   eqn:HWELLTYPED.
          { rewrite PeanoNat.Nat.eqb_eq in HWELLTYPED.
            destruct (Ir.Memory.get (Ir.Config.m st2) l)
              as [ mbl2 | ] eqn:HMBl2; try congruence.
            rewrite HWELLTYPED in HDEREF'.
            destruct (Ir.MemBlock.alive mbl2 && Ir.MemBlock.inbounds ofs mbl2 &&
                  Ir.MemBlock.inbounds (ofs + length (Ir.Byte.ofint (N.of_nat n0) n)) mbl2)
                     eqn:HRANGE; try congruence.
            destruct (Ir.MemBlock.n mbl2 <? ofs + length (Ir.Byte.ofint (N.of_nat n0) n)).
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
                  (Ir.MemBlock.set_bytes mbl2 ofs (Ir.Byte.ofint (N.of_nat n0) n))) blkid =
                      Ir.Memory.get (Ir.Config.m st1) blkid).
              { erewrite Ir.Memory.get_set_diff with (bid' := l) (mb := mb1)
                (m := Ir.Config.m st1); try congruence.
                { inv HWF1. assumption. }
                { reflexivity. }
              }
              rewrite HGET1.

              assert (HGET2:
                        Ir.Memory.get (Ir.Memory.set (Ir.Config.m st2) l
                  (Ir.MemBlock.set_bytes mbl2 ofs (Ir.Byte.ofint (N.of_nat n0) n))) blkid =
                      Ir.Memory.get (Ir.Config.m st2) blkid).
              { erewrite Ir.Memory.get_set_diff with (bid' := l) (mb := mb2)
                (m := Ir.Config.m st2); try congruence.
                { inv HWF2. assumption. }
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
          rewrite Ir.PTRSZ_def.
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
            { unfold Ir.Byte.ofptr. rewrite Ir.PTRSZ_def. reflexivity. }
            rewrite HPLEN' in *.
            (*rewrite HINB1.
            unfold Ir.PTRSZ in HINB2. simpl in HINB2.
            rewrite HINB2.
            simpl.*)
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
          }
          { (*unfold Ir.Byte.ofptr in HINB.
            rewrite Ir.PTRSZ_def in HINB.
            simpl in HINB.
            rewrite HINB.*)
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
    repeat (rewrite Ir.Config.m_update_m).
    assert (HTWIN5' := HTWIN5 bid').
    destruct t.
    { destruct HTWIN5'. exploit H0. assumption. intros HH.
      clear H H0.
      destruct v; try assumption.

      destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint (N.of_nat n0) n))
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
          { inv HWF1. assumption. }
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
          { inv HWF1. assumption. }
        }
        { rewrite PeanoNat.Nat.eqb_neq in HBID'.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { congruence. }
          { inv HWF1. assumption. }
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
        unfold Ir.ty_bitsz. rewrite Ir.PTRSZ_def. reflexivity. }

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
          { inv HWF1. assumption. }
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
          { inv HWF1. assumption. }
        }
        { rewrite PeanoNat.Nat.eqb_neq in HBID'.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          rewrite Ir.Memory.get_set_diff_short; try assumption.
          { inv HWF2. assumption. }
          { congruence. }
          { inv HWF1. assumption. }
          { congruence. }
        }
      }
    }
  }
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
    { apply Ir.Config.eq_wom_update_m. assumption. }
    split.
    { rewrite Ir.Config.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { rewrite Ir.Config.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { rewrite Ir.Config.m_update_m. unfold Ir.Memory.set.
      simpl. congruence. }
    split.
    { inv HWF1.
      intros. subst bid'.
      rewrite Ir.Config.m_update_m.
      eexists. eexists.
      split.
      { erewrite Ir.Memory.get_set_id_short.
        { reflexivity. }
        { eapply Ir.Memory.incr_time_wf.
          eassumption. reflexivity.
        }
        { rewrite Ir.Memory.get_incr_time_id. rewrite HH0. reflexivity. }
      }
      split.
      { rewrite Ir.Config.m_update_m.
        erewrite Ir.Memory.get_set_id_short.
        { reflexivity. }
        { inv HWF2. eapply Ir.Memory.incr_time_wf. eassumption.
          reflexivity. }
        { rewrite HH1. reflexivity. }
      }
      repeat (split; simpl; try congruence).
    }
    { (*bid' is not blkid. *)
      intros HDIFF.
      dup HDIFF.
      assert (HTWIN5' := HTWIN5 bid').
      destruct HTWIN5'. apply H0 in HDIFF. clear H H0.
      rewrite Ir.Config.m_update_m.
      rewrite Ir.Config.m_update_m.
      rewrite Ir.Memory.get_set_diff_short.
      rewrite Ir.Memory.get_set_diff_short.
      { unfold Ir.Memory.get.
        unfold Ir.Memory.get in HDIFF.
        unfold Ir.Memory.incr_time.
        simpl. assumption. }
      { inv HWF2.
        eapply Ir.Memory.incr_time_wf.
        eapply wf_m. reflexivity. }
      { assumption. }
      { inv HWF1.
        eapply Ir.Memory.incr_time_wf.
        eassumption. reflexivity.
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
    split. rewrite Ir.Config.m_update_m. simpl. congruence.
    split. rewrite Ir.Config.m_update_m. simpl. congruence.
    split. rewrite Ir.Config.m_update_m. simpl. congruence.
    split.
    { intros HDIFF2.
      subst bid'.
      rewrite Ir.Config.m_update_m.
      rewrite Ir.Config.m_update_m.
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
        { congruence. }
      }
      split.
      { erewrite Ir.Memory.get_set_diff_short; try eassumption.
        { inv HWF2.
          eapply Ir.Memory.incr_time_wf. eassumption.
          reflexivity. }
        { congruence. }
      }
      repeat (split; try congruence).
    }
    { intros HDIFF2.
      rewrite Ir.Config.m_update_m.
      rewrite Ir.Config.m_update_m.
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
        { inv HWF1.
          eapply Ir.Memory.incr_time_wf.
          eassumption. reflexivity. }
        { rewrite Ir.Memory.get_incr_time_id. rewrite HGET1. reflexivity. }
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
        { congruence. }
        { inv HWF1.
          eapply Ir.Memory.incr_time_wf; eauto. }
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


Lemma twin_state_cur_terminator_eq:
  forall (md:Ir.IRModule.t) (st1 st2:Ir.Config.t) blkid
         (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.cur_terminator md st1 = Ir.Config.cur_terminator md st2.
Proof.
  intros.
  inv HTWIN.
  unfold Ir.Config.cur_terminator.
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

Lemma twin_state_br_eq:
  forall md st1 st2 blkid n
         (HTWIN:twin_state st1 st2 blkid),
    twin_sresult (Ir.SmallStep.br md st1 n) (Ir.SmallStep.br md st2 n) blkid.
Proof.
  intros.
  unfold Ir.SmallStep.br.
  des_ifs; try
    ( eapply ts_goes_wrong; reflexivity).
  { rewrite twin_state_cur_fdef_pc_eq with (st2:= st2) (blkid := blkid) in Heq;
      try assumption.
    rewrite Heq in Heq1. inv Heq1.
    rewrite Heq0 in Heq2. inv Heq2.
    eapply ts_success; try reflexivity.
    eapply twin_state_update_pc. assumption.
  }
  { rewrite twin_state_cur_fdef_pc_eq with (st2:= st2) (blkid := blkid) in Heq;
      try assumption.
    rewrite Heq in Heq1. inv Heq1.
    rewrite Heq0 in Heq2. inv Heq2.
  }
  { rewrite twin_state_cur_fdef_pc_eq with (st2:= st2) (blkid := blkid) in Heq;
      try assumption.
    rewrite Heq in Heq1. inv Heq1.
  }
  { rewrite twin_state_cur_fdef_pc_eq with (st2:= st2) (blkid := blkid) in Heq;
      try assumption.
    rewrite Heq in Heq1. inv Heq1.
    rewrite Heq0 in Heq2. inv Heq2.
  }
  { rewrite twin_state_cur_fdef_pc_eq with (st2:= st2) (blkid := blkid) in Heq;
      try assumption.
    rewrite Heq in Heq0. inv Heq0.
  }
Qed.


Lemma twin_state_has_nestedcall_eq:
  forall st1 st2 blkid (HTWIN:twin_state st1 st2 blkid),
    Ir.Config.has_nestedcall st1 = Ir.Config.has_nestedcall st2.
Proof.
  intros.
  unfold Ir.Config.has_nestedcall.
  destruct st1. destruct st2.
  simpl in *.
  inv HTWIN.
  inv H.
  simpl in *.
  unfold Ir.Stack.eq in H1.
  destruct s; destruct s0; simpl; try (inv H1; fail); try reflexivity.
  inv H1.
  destruct s0; destruct s; simpl; try (inv H7; fail); try reflexivity.
Qed.

(* This lemma states that if (i, i+sz) is in mb1.P0 in state 1,
   (i, i+sz) is never in mb1.P0 in state 2, thanks to disjointness of
   twin blocks. *)
Lemma twin_state_inrange_false:
  forall md st1 st2 blkid i sz mb1 mb2
         (HTWIN:twin_state st1 st2 blkid)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (HSZ:sz > 0)
         (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid)
         (HGET2:Some mb2 = Ir.Memory.get (Ir.Config.m st2) blkid)
         (HINRANGE:in_range (i+sz)
                            (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true /\
                   in_range i (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true),
  ~ (in_range (i+sz) (List.hd (0, 0) (Ir.MemBlock.P_ranges mb2)) = true /\
     in_range i (List.hd (0, 0) (Ir.MemBlock.P_ranges mb2)) = true).
Proof.
  intros.
  inv HTWIN.
  clear H.
  destruct H0 as [H1 [H2 [H3 H4]]].
  assert (H4' := H4 blkid). clear H4.
  destruct H4'. clear H0. exploit H. reflexivity. intros HH. clear H.
  destruct HH as [mb1' [mb2' [HH1 [HH2 HH]]]].
  rewrite <- HGET1 in HH1. inv HH1.
  rewrite <- HGET2 in HH2. inv HH2.
  destruct HH as [HH1 [HH2 [HH3 [HH4 [HH5 [HH6 HH7]]]]]].
  (* get the disjointness criteria. *)
  inv HWF1.
  clear wf_cid_to_f wf_cid_to_f2 wf_stack wf_ptr wf_ptr_mem.
  inv wf_m.
  dup HGET1.
  apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HGET0;
    try reflexivity.
  apply wf_blocks in HGET0.
  clear wf_uniqueid wf_newid wf_disjoint wf_blocktime_beg wf_blocktime_end.
  inv HGET0.
  remember (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) as P1.
  remember (List.hd (0, 0) (Ir.MemBlock.P_ranges mb2)) as P2.
  unfold Ir.TWINCNT in *.
  (* show that Ir.MemBlock.P isn't empty *)
  destruct (Ir.MemBlock.P mb1) as [ | Ph1 Pt1] eqn:Hmb1;
  destruct (Ir.MemBlock.P mb2) as [ | Ph2 Pt2] eqn:Hmb2;
  try inv wf_twin.
  { apply Permutation_length in HH6. inv HH6. }
  { simpl in *.
    (* P_ranges isn't empty. *)
    destruct (Ir.MemBlock.P_ranges mb1) as [ | Prh1 Prt1] eqn:Hmbr1;
      destruct (Ir.MemBlock.P_ranges mb2) as [ | Prh2 Prt2] eqn:Hmbr2.
    { unfold Ir.MemBlock.P_ranges in *.
      rewrite Hmb2 in Hmbr2. inv Hmbr2. }
    { unfold Ir.MemBlock.P_ranges in *.
      rewrite Hmb1 in Hmbr1. inv Hmbr1. }
    { unfold Ir.MemBlock.P_ranges in *.
      rewrite Hmb2 in Hmbr2. inv Hmbr2. }
    { (* Okay, cool.*)
      assert (HPERM':Permutation (Ir.MemBlock.P_ranges mb1)
                                 (Ir.MemBlock.P_ranges mb2)).
      { unfold Ir.MemBlock.P_ranges.
        rewrite HH3.
        eapply map_Permutation.
        congruence. }
      assert (HDR:disjoint_range (Ph1, Ir.MemBlock.n mb2)
                                 (Ph2, Ir.MemBlock.n mb2) = true).
      { assert (List.In (Ph1, Ir.MemBlock.n mb2) (Ir.MemBlock.P_ranges mb1)).
        { unfold Ir.MemBlock.P_ranges.
          rewrite Hmb1. simpl. left. congruence. }
        assert (List.In (Ph2, Ir.MemBlock.n mb2) (Ir.MemBlock.P_ranges mb2)).
        { unfold Ir.MemBlock.P_ranges.
          rewrite Hmb2. simpl. left. congruence. }
        eapply disjoint_ranges_In.
        { apply wf_disj. }
        { rewrite Hmbr1 in H. assumption. }
        { eapply Permutation_in.
          { apply Permutation_sym in HPERM'.
            rewrite Hmbr1 in HPERM'.
            rewrite Hmbr2 in HPERM'.
            eapply HPERM'. }
          { rewrite Hmbr2 in H4. assumption. }
        }
        { intros HH. congruence. }
      }
      unfold disjoint_range in HDR.
      rewrite orb_true_iff in HDR.
      rewrite PeanoNat.Nat.leb_le in HDR.
      rewrite PeanoNat.Nat.leb_le in HDR.
      unfold in_range in *.
      destruct HINRANGE as [HIR1 HIR2].
      rewrite andb_true_iff in HIR1.
      rewrite andb_true_iff in HIR2.
      simpl in HIR1. simpl in HIR2.
      repeat (rewrite PeanoNat.Nat.leb_le in HIR1).
      repeat (rewrite PeanoNat.Nat.leb_le in HIR2).
      simpl.
      assert (HPrh1: Prh1 = (Ph1, Ir.MemBlock.n mb2)).
      { unfold Ir.MemBlock.P_ranges in Hmbr1.
        rewrite Hmb1 in Hmbr1. simpl in Hmbr1. inv Hmbr1.
        congruence. }
      assert (HPrh2: Prh2 = (Ph2, Ir.MemBlock.n mb2)).
      { unfold Ir.MemBlock.P_ranges in Hmbr2.
        rewrite Hmb2 in Hmbr2. simpl in Hmbr2. inv Hmbr2.
        reflexivity. }
      rewrite HPrh1 in HIR1, HIR2.
      rewrite HPrh2.
      simpl. simpl in HIR1, HIR2.
      intros HH0'.
      destruct HH0' as [HH1' HH2'].
      rewrite andb_true_iff in HH1'.
      rewrite andb_true_iff in HH2'.
      rewrite PeanoNat.Nat.leb_le in HH1'.
      rewrite PeanoNat.Nat.leb_le in HH1'.
      rewrite PeanoNat.Nat.leb_le in HH2'.
      rewrite PeanoNat.Nat.leb_le in HH2'.
      destruct HDR; omega.
    }
  }
Qed.

Lemma inbounds_abs_canonicalize:
  forall m mb1 bid o sz
         (HGET:Some mb1 = Ir.Memory.get m bid)
         (HWF:Ir.Memory.wf m),
    (Ir.MemBlock.inbounds_abs o mb1 &&
     Ir.MemBlock.inbounds_abs (o + sz) mb1 = true)
    <->
    ((in_range (o+sz) (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true /\
      in_range o (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true)).
Proof.
  intros.
  split.
  { intros HINB.
    unfold Ir.MemBlock.inbounds_abs in HINB.
    unfold Ir.MemBlock.P0_range in HINB.
    unfold Ir.MemBlock.addr in HINB.
    unfold Ir.MemBlock.P_ranges.
    inv HWF.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks m)
      in HGET.
    apply wf_blocks in HGET.
    inv HGET. unfold Ir.TWINCNT in wf_twin.
    destruct (Ir.MemBlock.P mb1).
    simpl in wf_twin. inv wf_twin.
    simpl in HINB. simpl.
    rewrite andb_true_iff in HINB.
    intuition.
    reflexivity.
  }
  { intros.
    unfold Ir.MemBlock.inbounds_abs.
    unfold Ir.MemBlock.P0_range.
    unfold Ir.MemBlock.addr.
    unfold Ir.MemBlock.P_ranges in H.
    inv HWF.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks m)
        in HGET.
    apply wf_blocks in HGET.
    inv HGET. unfold Ir.TWINCNT in wf_twin.
    destruct (Ir.MemBlock.P mb1).
    simpl in wf_twin. inv wf_twin.
    simpl in H. simpl.
    rewrite andb_true_iff.
    intuition.
    reflexivity.
  }
Qed.

Lemma twin_state_inbounds_abs_reserved:
  forall st1 st2 blkid mb1 o sz md
         (HTWIN:twin_state st1 st2 blkid)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (HSZ:sz > 0)
         (HALIVE:Ir.MemBlock.alive mb1 = true)
         (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid)
         (HINB:Ir.MemBlock.inbounds_abs o mb1 &&
               Ir.MemBlock.inbounds_abs (o + sz) mb1 = true),
    ~ exists bid2 mb2,
        (Ir.Memory.get (Ir.Config.m st2) bid2 = Some mb2 /\
         Ir.MemBlock.alive mb2 = true /\
         Ir.MemBlock.inbounds_abs o mb2 &&
         Ir.MemBlock.inbounds_abs (o + sz) mb2 = true).
Proof.
  intros.
  intros HCONTRA.
  destruct HCONTRA as [bid2 [mb2 [HGET2 [HALIVE2 HINB2]]]].
  destruct (blkid =? bid2) eqn:HEQ.
  { rewrite PeanoNat.Nat.eqb_eq in HEQ.

    dup HWF1. dup HWF2.
    inv HWF1. inv HWF2.
    symmetry in HGET2.
    rewrite inbounds_abs_canonicalize in HINB; try eassumption.
    eapply twin_state_inrange_false with (md := md) (st1 := st1) (st2 := st2)
      (mb2 := mb2) in HINB;
      try assumption.
    rewrite inbounds_abs_canonicalize in HINB2; try eassumption.
    congruence.
    { eassumption. }
    { eassumption. }
    { eassumption. }
  }
  { symmetry in HGET2.
    assert (Some mb2 = Ir.Memory.get (Ir.Config.m st1) bid2).
    { decompose_HTWIN HTWIN bid2.
      destruct HTWIN5'. exploit H0. rewrite PeanoNat.Nat.eqb_neq in HEQ.
      congruence. intros HH. clear H H0.
      congruence. }
    rewrite inbounds_abs_canonicalize in HINB; try eassumption.
    rewrite inbounds_abs_canonicalize in HINB2; try eassumption.
    remember ((List.hd (0, 0) (Ir.MemBlock.P_ranges mb1))) as P1.
    remember ((List.hd (0, 0) (Ir.MemBlock.P_ranges mb2))) as P2.
    destruct HINB.
    destruct HINB2.
    assert (disjoint_range P1 P2 = true).
    { inv HWF1.
      clear wf_cid_to_f wf_cid_to_f2 wf_stack wf_ptr_mem.
      clear wf_ptr.
      rewrite Ir.MemBlock.P_ranges_hd_P0_range.
      rewrite Ir.MemBlock.P_ranges_hd_P0_range.
      eapply Ir.Memory.disjoint_range_P0_range with (m := Ir.Config.m st1); try eassumption.
      { rewrite PeanoNat.Nat.eqb_neq in HEQ. congruence. }
      { inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in H. eassumption.
        reflexivity. }
      { inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in HGET1. eassumption.
        reflexivity. }
    }
    unfold disjoint_range in H4.
    destruct P1. destruct P2.
    unfold in_range in *.
    simpl in *.
    rewrite andb_true_iff in *.
    rewrite orb_true_iff in H4.
    repeat (rewrite PeanoNat.Nat.leb_le in *).
    destruct H4. omega. omega.
    inv HWF1. assumption. inv HWF1. assumption.
  }
Qed.

(* This lemma states that if (i, i+sz) is in mb1.P0 in state 1,
   (i, i+sz) is in P' s.t. P' \in mb1.P /\ P' != mb1.P0, in state 2. *)
Lemma twin_state_inrange_nonP0:
  forall md st1 st2 blkid i sz mb1 mb2
         (HTWIN:twin_state st1 st2 blkid)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (HSZ:sz > 0)
         (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid)
         (HGET2:Some mb2 = Ir.Memory.get (Ir.Config.m st2) blkid)
         (HINRANGE:in_range (i+sz)
                            (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true /\
                   in_range i (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) = true),
  exists r, (List.In r (Ir.MemBlock.P_ranges mb2) /\
             r <> List.hd (0, 0) (Ir.MemBlock.P_ranges mb2) /\
             in_range i r = true /\
             in_range (i+sz) r = true).
Proof.
  intros.
  inv HTWIN.
  clear H.
  destruct H0 as [H1 [H2 [H3 H4]]].
  assert (H4' := H4 blkid). clear H4.
  destruct H4'. clear H0. exploit H. reflexivity. intros HH. clear H.
  destruct HH as [mb1' [mb2' [HH1 [HH2 HH]]]].
  rewrite <- HGET1 in HH1. inv HH1.
  rewrite <- HGET2 in HH2. inv HH2.
  destruct HH as [HH1 [HH2 [HH3 [HH4 [HH5 [HH6 HH7]]]]]].
  (* get the disjointness criteria. *)
  inv HWF1.
  clear wf_cid_to_f wf_cid_to_f2 wf_stack wf_ptr wf_ptr_mem.
  inv wf_m.
  dup HGET1.
  apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st1)) in HGET0;
    try reflexivity.
  apply wf_blocks in HGET0.
  clear wf_uniqueid wf_newid wf_disjoint wf_blocktime_beg wf_blocktime_end.
  inv HGET0.
  remember (List.hd (0, 0) (Ir.MemBlock.P_ranges mb1)) as P1.
  remember (List.hd (0, 0) (Ir.MemBlock.P_ranges mb2)) as P2.
  unfold Ir.TWINCNT in *.
  (* show that Ir.MemBlock.P isn't empty *)
  destruct (Ir.MemBlock.P mb1) as [ | Ph1 Pt1] eqn:Hmb1;
  destruct (Ir.MemBlock.P mb2) as [ | Ph2 Pt2] eqn:Hmb2;
  try inv wf_twin.
  { apply Permutation_length in HH6. inv HH6. }

  simpl in *.
  (* P_ranges isn't empty. *)
  destruct (Ir.MemBlock.P_ranges mb1) as [ | Prh1 Prt1] eqn:Hmbr1;
    destruct (Ir.MemBlock.P_ranges mb2) as [ | Prh2 Prt2] eqn:Hmbr2.
  { unfold Ir.MemBlock.P_ranges in *.
    rewrite Hmb2 in Hmbr2. inv Hmbr2. }
  { unfold Ir.MemBlock.P_ranges in *.
    rewrite Hmb1 in Hmbr1. inv Hmbr1. }
  { unfold Ir.MemBlock.P_ranges in *.
    rewrite Hmb2 in Hmbr2. inv Hmbr2. }
  (* Okay, cool.*)
  assert (HPERM':Permutation (Ir.MemBlock.P_ranges mb1)
                             (Ir.MemBlock.P_ranges mb2)).
  { unfold Ir.MemBlock.P_ranges.
    rewrite HH3.
    eapply map_Permutation.
    congruence. }
  rewrite Hmbr1, Hmbr2 in HPERM'.
  assert (Prh1 <> Prh2).
  {
    unfold Ir.MemBlock.P_ranges in Hmbr1, Hmbr2.
    rewrite Hmb2 in Hmbr2.
    rewrite Hmb1 in Hmbr1.
    simpl in Hmbr1. inv Hmbr1. simpl in Hmbr2. inv Hmbr2.
    congruence. }
  assert (List.In Prh1 Prt2).
  { eapply Permutation_in with (x := Prh1) in HPERM'.
    { inversion HPERM'. congruence. congruence. }
    { constructor. reflexivity. }
  }
  exists Prh1.
  split. right. assumption.
  split. simpl. congruence.
  simpl in HINRANGE.
  destruct HINRANGE.
  split. assumption.
  assumption.
Qed.

(* This lemma states that if state st1 dereferences blkid,
   twin state st2 dereferences nothing (which means UB). *)
Lemma twin_state_get_deref:
  forall md st1 st2 blkid mb1 ofs  o I cid bwid
         (HTWIN:twin_state st1 st2 blkid)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (HMB1:Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid)
         (HSZ:bwid > 0)
         (HDEREF1:Ir.get_deref (Ir.Config.m st1) (Ir.pphy o I cid) bwid =
                  [(blkid, mb1, ofs)]),
    Ir.get_deref (Ir.Config.m st2) (Ir.pphy o I cid) bwid = nil.
Proof.
  intros.
  dup HDEREF1.
  eapply Ir.get_deref_inv in HDEREF1.
  { remember (Ir.get_deref (Ir.Config.m st2) (Ir.pphy o I cid) bwid) as l'.
    symmetry in Heql'.
    dup Heql'.
    eapply Ir.get_deref_phy_singleton in Heql'.
    destruct Heql'.
    { destruct H. destruct H. inv H. destruct H0.
      destruct x. destruct p. simpl in H.
      simpl in H0.
      eapply Ir.get_deref_inv in H1.
      (* okay , now use twin_state_inbounds_abs_reserved! *)
      rewrite <- andb_assoc in HDEREF1.
      rewrite andb_true_iff in HDEREF1. destruct HDEREF1.
      erewrite Ir.MemBlock.inbounds_inbounds_abs in H3; try reflexivity.
      erewrite Ir.MemBlock.inbounds_inbounds_abs in H3; try reflexivity.
      rewrite <- PeanoNat.Nat.add_assoc in H3.
      rewrite PeanoNat.Nat.add_comm with (n := bwid) in H3.
      rewrite PeanoNat.Nat.add_assoc in H3.
      dup H3.
      eapply twin_state_inbounds_abs_reserved with (st2 := st2) (sz := bwid) in H2.
      { exfalso. eapply H2.
        exists b. exists t.
        split.
        { eassumption. }
        rewrite andb_true_iff in H1. rewrite andb_true_iff in H1.
        destruct H1. destruct H1.
        split.
        { assumption. }
        { erewrite Ir.MemBlock.inbounds_inbounds_abs in H5; try reflexivity.
          erewrite Ir.MemBlock.inbounds_inbounds_abs in H6; try reflexivity.
          rewrite <- PeanoNat.Nat.add_assoc in H5.
          rewrite PeanoNat.Nat.add_comm with (n := bwid) in H5.
          rewrite PeanoNat.Nat.add_assoc in H5.
          rewrite H6. rewrite H5. reflexivity.
        }
      }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { eassumption. }
      { apply Ir.get_deref_phy_singleton in HDEREF0.
        destruct HDEREF0.
        { destruct H5. destruct H5. inv H5. simpl in H6.
          destruct H6. rewrite PeanoNat.Nat.add_comm with (m := n) in H5.
          rewrite H5. rewrite PeanoNat.Nat.add_comm with (m := ofs).
          assumption. }
        { inv H5. }
        { inv HWF1. assumption. }
        { omega. }
      }
      { eassumption. }
      { inv HWF2. assumption. }
      { assumption. }
    }
    { assumption. }
    { inv HWF2. assumption. }
    { omega. }
  }
  { omega. }
  { inv HWF1. assumption. }
  { congruence. }
Qed.

End Ir.

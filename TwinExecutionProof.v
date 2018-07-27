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
Require Import SmallStepAux.
Require Import SmallStepWf.
Require Import Reordering.
Require Import TwinExecution.
Require Import TwinExecutionAux.


Module Ir.

Import TwinExecution.
Import Ir.

(*******************************************************
                 Main Theorems 
 *******************************************************)


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
    rewrite Ir.SmallStep.get_val_update_reg_and_incrpc_samereg. reflexivity. assumption. }
  { (* malloc succeeded. *)
    right.
    rewrite <- HCUR in HCUR0.
    inv HCUR0.
    (* Let's make P' which is permutated P. *)
    dup HMBWF.
    assert (HMBWF' := HMBWF (Ir.Memory.mt (Ir.Config.m st))).
    clear HMBWF.
    inv HMBWF'.
    rewrite Ir.SmallStep.get_val_update_reg_and_incrpc_samereg.
    simpl in *.
    destruct P as [ | p1 P]; try (inv wf_twin; fail).
    destruct P as [ | p2 P]; try (inv wf_twin; fail).
    exists (Ir.SmallStep.update_reg_and_incrpc md
        (Ir.Config.update_m st
          (fst (Ir.Memory.new (Ir.Config.m st) (Ir.heap) nsz
                       (Ir.SYSALIGN) (List.repeat Ir.Byte.poison nsz)
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
        rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
        rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
        apply Ir.Config.eq_wom_update_m.
        apply Ir.Config.eq_wom_refl.
      }
      { repeat (rewrite Ir.SmallStep.update_reg_and_incrpc_update_m).
        repeat (rewrite Ir.Config.m_update_m).
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
            destruct (nsz). omega.
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
      

Import TwinExecutionAux.
Import Ir.

Ltac thats_it := apply twin_state_update_reg_and_incrpc;
            assumption.

Ltac coalesce_op Hop1 Hop2 st2 HTWIN :=
  assert (Htmp := Hop1);
  assert (Htmp2 := Hop2);
  erewrite twin_state_get_val_eq with (st2 := st2) in Htmp;
  try apply HTWIN;
  rewrite Htmp in Htmp2; inv Htmp2; clear Htmp.



Opaque Ir.MEMSZ.
Opaque Ir.PTRSZ.

(* Lemma: If (1) input states are twin-state &
   (2) current instruction don't do memory access from a guessed pointer &
   (3) current instruction never observes the twin block id,
   each step on the two input states make twin state as well.
   Note that in this lemma instruction is limited to
   non-phi, non-terminator instructions (by definition of inst_step).
   For phi / terminator: see the next lemmas. *)
Lemma twin_execution_inst_unidir:
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
                  in Heqoi2; try (apply twin_state_sym in HTWIN; assumption).
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
                  in Heqoi2; try (apply twin_state_sym in HTWIN; assumption).
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
        { inv H0. eapply ts_success. reflexivity. reflexivity. reflexivity.
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
            {reflexivity. } { reflexivity. } { reflexivity. }
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
      { (* deref. poison *)
        inv H0.
        erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
          try apply HTWIN.
        eexists . split. 
        { eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1.
          rewrite Hop11. reflexivity. }
        { eapply ts_goes_wrong; try reflexivity. }
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
            { reflexivity. }
            { eapply twin_state_incrpc.
              erewrite twin_state_get_val_eq with (st2 := st2) in Hop12;
                try apply HTWIN.
              rewrite Hop12 in Hop22. inv Hop22.
              eapply twin_state_store_val; try eassumption.
              { apply Ir.ty_bytesz_pos. }
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
        { (* ptr is poison. *)
          erewrite twin_state_get_val_eq with (st2 := st2) in Hop11;
            try apply HTWIN.
          eexists.
          split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1.
            rewrite Hop11. rewrite Hop22.
            reflexivity. }
          { constructor; reflexivity. }
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
            reflexivity. reflexivity. reflexivity.
            apply twin_state_incrpc. assumption. }
        }
        { inv H0.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1. rewrite Hop21. rewrite Hop22. reflexivity.
          }
          { eapply ts_success.
            reflexivity. reflexivity. reflexivity.
            apply twin_state_incrpc. assumption. }
        }
        { inv H0.
          eexists. split.
          { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite <- Heqoi1. rewrite Hop21. rewrite Hop22. reflexivity.
          }
          { eapply ts_success.
            reflexivity. reflexivity. reflexivity.
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
          reflexivity. reflexivity. reflexivity.
          apply twin_state_incrpc. assumption. }
      }
      { (* all ops are none.*)
        inv H0.
        eexists. split.
        { apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
          rewrite <- Heqoi1. rewrite Hop21. reflexivity.
        }
        { eapply ts_success.
          reflexivity. reflexivity. reflexivity.
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
              { eapply ts_success. reflexivity. reflexivity. reflexivity.
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
        eapply ts_success. reflexivity. reflexivity. reflexivity.
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
        eapply ts_success. reflexivity. reflexivity. reflexivity.
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
                inversion H0.
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
          rewrite twin_state_allocatable_eq with (st2 := st1) (blkid := blkid)
            (md := md) in H.
          exists x. assumption.
          apply twin_state_sym. assumption.
          assumption. assumption.
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
        { rewrite <- twin_state_allocatable_eq with (st1 := st1) (blkid := blkid)
          (md := md);
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
        { rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          eapply Ir.Config.eq_wom_update_m.

          eapply Ir.SmallStep.eq_wom_update_reg_and_incrpc. assumption.
        }
        split.
        { rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          simpl. reflexivity. }
        split.
        { rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          simpl. reflexivity. }
        split.
        { rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          rewrite Ir.SmallStep.update_reg_and_incrpc_update_m.
          rewrite Ir.Config.m_update_m.
          simpl. reflexivity. }
        rewrite Ir.SmallStep.m_update_reg_and_incrpc.
        rewrite Ir.SmallStep.m_update_reg_and_incrpc.
        rewrite Ir.Config.m_update_m.
        rewrite Ir.Config.m_update_m.
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
  { (* icmp, nondet *)
    rewrite twin_state_icmp_eq_ptr_nondet_cond_eq
      with (st2 := st2) (blkid := blkid) in HNONDET;
      try assumption.
    rewrite twin_state_get_val_eq
      with (st2 := st2) (blkid := blkid) in HOP1;
      try assumption.
    rewrite twin_state_get_val_eq
      with (st2 := st2) (blkid := blkid) in HOP2;
      try assumption.
    rewrite twin_state_cur_inst_eq
      with (st2 := st2) (blkid := blkid) in HCUR;
      try assumption.
    eexists. split.
    { eapply Ir.SmallStep.s_icmp_eq_nondet.
      { rewrite HCUR. reflexivity. }
      { reflexivity. }
      { rewrite HOP1. reflexivity. }
      { rewrite HOP2. reflexivity. }
      { eassumption. }
    }
    { eapply ts_success; try reflexivity.
      thats_it. }
  }
  { (* icmp, ule, nondet *)
    rewrite twin_state_icmp_ule_ptr_nondet_cond_eq
      with (st2 := st2) (blkid := blkid) in HNONDET;
      try assumption.
    rewrite twin_state_get_val_eq
      with (st2 := st2) (blkid := blkid) in HOP1;
      try assumption.
    rewrite twin_state_get_val_eq
      with (st2 := st2) (blkid := blkid) in HOP2;
      try assumption.
    rewrite twin_state_cur_inst_eq
      with (st2 := st2) (blkid := blkid) in HCUR;
      try assumption.
    eexists. split.
    { eapply Ir.SmallStep.s_icmp_ule_nondet.
      { rewrite HCUR. reflexivity. }
      { reflexivity. }
      { rewrite HOP1. reflexivity. }
      { rewrite HOP2. reflexivity. }
      { eassumption. }
    }
    { eapply ts_success; try reflexivity.
      thats_it. }
  }
Qed.


(* Lemma same as twin_execution_inst_unidir, but
   with phi nodes this time .*)
Lemma twin_execution_phi_unidir:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
         (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (* Input state st1 and st2 are twin-state. *)
         (HTWIN:twin_state st1 st2 blkid),
    (* one way dir *)
    forall bef_bbid st1' (HSTEP1:Ir.SmallStep.phi_bigstep md bef_bbid st1 st1'),
          exists st2', Ir.SmallStep.phi_bigstep md bef_bbid st2 st2' /\
                      twin_state st1' st2' blkid.
Proof.
  intros.
  generalize dependent HWF1.
  generalize dependent HWF2.
  induction HSTEP1.
  { intros.
    unfold Ir.SmallStep.phi_step in HSTEP.
    des_ifs.
    eexists. split.
    { eapply Ir.SmallStep.pbs_one.
      unfold Ir.SmallStep.phi_step.
      rewrite twin_state_cur_phi_eq with (st2 := st2) (blkid := blkid) in Heq;
        try assumption.
      rewrite Heq.
      rewrite Heq0.
      rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in Heq1;
        try assumption.
      rewrite Heq1.
      reflexivity.
    }
    { thats_it. }
  }
  { intros.
    exploit IHHSTEP1. assumption. assumption. assumption.
    intros H.
    destruct H as [st2' H].
    destruct H. clear IHHSTEP1.
    unfold Ir.SmallStep.phi_step in HSTEP.
    des_ifs.
    eexists.
    split.
    { eapply Ir.SmallStep.pbs_succ.
      eassumption.
      unfold Ir.SmallStep.phi_step.
      rewrite twin_state_cur_phi_eq with (st2 := st2') (blkid := blkid) in Heq;
        try assumption.
      rewrite Heq.
      rewrite Heq0.
      rewrite twin_state_get_val_eq with (st2 := st2') (blkid := blkid) in Heq1;
        try assumption.
      rewrite Heq1. reflexivity.
    }
    { thats_it. }
  }
Qed.


(* Lemma same as twin_execution_inst_unidir, but
   with terminators this time .*)
Lemma twin_execution_terminator_unidir:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
         (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (* Input state st1 and st2 are twin-state. *)
         (HTWIN:twin_state st1 st2 blkid),
    (* one way dir *)
    forall sr1 (HSTEP1:Ir.SmallStep.t_step md st1 = sr1),
          exists sr2, Ir.SmallStep.t_step md st2 = sr2 /\
                      twin_sresult sr1 sr2 blkid.
Proof.
  intros.
  unfold Ir.SmallStep.t_step in HSTEP1.
  destruct (Ir.Config.cur_terminator md st1) eqn:HTERM.
  {
    destruct t.
    { (* tbr *)
      eexists. split.
      unfold Ir.SmallStep.t_step.
      rewrite twin_state_cur_terminator_eq with (st2 := st2) (blkid := blkid) in HTERM;
        try assumption.
      rewrite HTERM. reflexivity.
      rewrite <- HSTEP1.
      eapply twin_state_br_eq. assumption. }
    { (* tbr_cond. *)
      destruct (Ir.Config.get_val st1 o) eqn:HOP1.
      { destruct v.
        { destruct ((n1 =? 0)) eqn:HN.
          { eexists. split.
            unfold Ir.SmallStep.t_step.
            rewrite twin_state_cur_terminator_eq
              with (st2 := st2) (blkid := blkid) in HTERM;
              try assumption.
            rewrite HTERM. reflexivity.
            rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
              try assumption.
            rewrite HOP1. rewrite <- HSTEP1. rewrite HN.
            eapply twin_state_br_eq. assumption. 
          }
          { eexists. split.
            unfold Ir.SmallStep.t_step.
            rewrite twin_state_cur_terminator_eq
              with (st2 := st2) (blkid := blkid) in HTERM;
              try assumption.
            rewrite HTERM. reflexivity.
            rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
              try assumption.
            rewrite HOP1. rewrite <- HSTEP1. rewrite HN.
            eapply twin_state_br_eq. assumption. 
          }
        }
        { eexists. split.
          { unfold Ir.SmallStep.t_step.
            rewrite twin_state_cur_terminator_eq
              with (st2 := st2) (blkid := blkid) in HTERM;
              try assumption.
            rewrite HTERM. reflexivity. }
          { 
            rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
              try assumption.
            rewrite HOP1. rewrite <- HSTEP1.
            eapply ts_goes_wrong; reflexivity.
          }
        }
        { eexists. split.
          { unfold Ir.SmallStep.t_step.
            rewrite twin_state_cur_terminator_eq
              with (st2 := st2) (blkid := blkid) in HTERM;
              try assumption.
            rewrite HTERM. reflexivity. }
          { 
            rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
              try assumption.
            rewrite HOP1. rewrite <- HSTEP1.
            eapply ts_goes_wrong; reflexivity.
          }
        }
      }
      { eexists. split.
        { unfold Ir.SmallStep.t_step.
          rewrite twin_state_cur_terminator_eq
            with (st2 := st2) (blkid := blkid) in HTERM;
            try assumption.
          rewrite HTERM. reflexivity. }
        { 
          rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
            try assumption.
          rewrite HOP1. rewrite <- HSTEP1.
          eapply ts_goes_wrong; reflexivity.
        }
      }
    }
    { (* tret *)
      eexists. split.
      { unfold Ir.SmallStep.t_step.
        rewrite twin_state_cur_terminator_eq
          with (st2 := st2) (blkid := blkid) in HTERM;
          try assumption.
        rewrite HTERM. reflexivity. }
      {
        destruct (Ir.Config.get_val st1 o) eqn:HOP1.
        {
          rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
            try assumption.
          rewrite HOP1.
          rewrite twin_state_has_nestedcall_eq with (st2:= st2) (blkid := blkid)
                                            in HSTEP1; try assumption.
          rewrite <- HSTEP1.
          des_ifs.
          { eapply ts_goes_wrong; reflexivity. }
          { eapply ts_prog_finish; try reflexivity. }
        }
        { 
          rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in HOP1;
            try assumption.
          rewrite HOP1.
          rewrite <- HSTEP1.
          eapply ts_goes_wrong; reflexivity.
        }
      }
    }
  }
  { eexists. split.
    { reflexivity. }
    { unfold Ir.SmallStep.t_step.
      rewrite twin_state_cur_terminator_eq with (st2 := st2) (blkid := blkid)
        in HTERM; try assumption.
      rewrite HTERM. rewrite <- HSTEP1.
      eapply ts_goes_wrong; reflexivity.
    }
  }
Qed.


(* twin_execution_inst_unidir +
   twin_execution_phi_unidir +
   twin_execution_terminator_unidir *)
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
    forall sr1 (HSTEP1:Ir.SmallStep.sstep md st1 sr1),
          exists sr2, Ir.SmallStep.sstep md st2 sr2 /\
                      twin_sresult sr1 sr2 blkid.
Proof.
  intros.
  inv HSTEP1.
  { assert (exists sr3 : Ir.SmallStep.step_res,
    Ir.SmallStep.inst_step md st2 sr3 /\ twin_sresult sr0 sr3 blkid).
    { apply twin_execution_inst_unidir with (st1 := st1) (st2 := st2); try assumption.
    }
    destruct H. destruct H.
    exists x.
    split. eapply Ir.SmallStep.ss_inst. assumption. assumption.
  }
  { assert (exists sr3 : Ir.SmallStep.step_res,
    Ir.SmallStep.t_step md st2 = sr3 /\ twin_sresult Ir.SmallStep.sr_goes_wrong
                                                   sr3 blkid).
    { apply twin_execution_terminator_unidir with
          (st1 := st1) (st2 := st2); try assumption.
    }
    destruct H. destruct H.
    exists x.
    split.
    inv H0; try congruence.
    { rewrite HSR0. eapply Ir.SmallStep.ss_br_goes_wrong.
      erewrite twin_state_cur_terminator_eq in HCUR. eassumption.
      eassumption. eassumption. }
    { assumption. }
  }
  { assert (exists sr : Ir.SmallStep.step_res,
    Ir.SmallStep.t_step md st2 = sr /\
    twin_sresult (Ir.SmallStep.sr_success Ir.e_none st') sr blkid).
    { eapply twin_execution_terminator_unidir.
      eassumption.
      eassumption.
      eapply HWF1.
      eassumption.
      eassumption.
      eassumption.
    }
    destruct H. destruct H.
    dup H0.
    inv H1; try congruence.
    inv HSR1.
    assert (HWF0:Ir.Config.wf md st0).
    { eapply Ir.SmallStep.t_step_wf. eapply HWF1. eassumption. }
    assert (HWF3:Ir.Config.wf md st3).
    { eapply Ir.SmallStep.t_step_wf. eapply HWF2. eassumption. }
    assert (exists st',
       Ir.SmallStep.phi_bigstep md (Ir.SmallStep.pc_bbid pc0) st3 st' /\
       twin_state st'' st' blkid).
    { eapply twin_execution_phi_unidir.
      assumption.
      assumption.
      eapply HWF0. assumption. assumption. assumption. }
    destruct H. destruct H.
    rewrite HSR2 in H0.
    exists (Ir.SmallStep.sr_success Ir.e_none x).
    split. eapply Ir.SmallStep.ss_br_success. eassumption.
    erewrite twin_state_cur_fdef_pc_eq with (st2 := st1). eassumption.
    apply twin_state_sym in HTWIN. eassumption. eassumption.
    erewrite twin_state_cur_fdef_pc_eq with (st2 := st''). eassumption.
    apply twin_state_sym in H1. eassumption. eassumption.
    eapply ts_success; try reflexivity. assumption.
  }
Qed.


(* The main theorem *)
Theorem twin_execution:
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
    (* Bisimulation. *)
    (forall sr1 (HSTEP1:Ir.SmallStep.sstep md st1 sr1),
          exists sr2, Ir.SmallStep.sstep md st2 sr2 /\
                      twin_sresult sr1 sr2 blkid) /\
    (forall sr2 (HSTEP1:Ir.SmallStep.sstep md st2 sr2),
          exists sr1, Ir.SmallStep.sstep md st1 sr1 /\
                      twin_sresult sr1 sr2 blkid).
Proof.
  intros.
  split.
  { eapply twin_execution_unidir; try assumption. }
  { assert (forall sr0 : Ir.SmallStep.step_res,
               Ir.SmallStep.sstep md st2 sr0 ->
      exists sr3 : Ir.SmallStep.step_res,
        Ir.SmallStep.sstep md st1 sr3 /\ twin_sresult sr0 sr3 blkid).
    { eapply twin_execution_unidir; try eassumption.
      apply twin_state_sym. assumption.
      { intros HH. apply HNOGUESSEDACCESS.
        inv HH.
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOPPTR; try assumption.
          eapply gp_store; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOPPTR; try assumption.
          eapply gp_load; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOPPTR; try assumption.
          eapply gp_free; try eassumption. }
      }
      { intros HH. apply HNOTOBSERVE.
        inv HH.
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          eapply ob_by_ptrtoint; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_iicmpeq_l; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_iicmpeq_r; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_iicmpule_l; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_iicmpule_r; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_psub_l; try eassumption. }
        { rewrite <- twin_state_cur_inst_eq with (st1 := st1) (blkid := blkid)
            in HINST; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP1; try assumption.
          rewrite <- twin_state_get_val_eq with (st1 := st1) (blkid := blkid)
            in HOP2; try assumption.
          eapply ob_by_psub_r; try eassumption. }
      }
    }
    intros.
    assert (H' := H sr0 HSTEP1).
    destruct H'.
    destruct H0.
    exists x. split. assumption.
    inv H1.
    { eapply ts_success; try reflexivity.
      apply twin_state_sym. assumption. }
    { eapply ts_goes_wrong; try reflexivity. }
    { eapply ts_oom; try reflexivity. }
    { eapply ts_prog_finish; try reflexivity. }
  }
Qed.






(* Show that memory access from guessed pointer succeeds in
   one of twin state, it fails in the other state. *)
Theorem access_from_guessed_pointer_fails:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
         (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
         (HWF1:Ir.Config.wf md st1)
         (HWF2:Ir.Config.wf md st2)
         (* Input state st1 and st2 are twin-state. *)
         (HTWIN:twin_state st1 st2 blkid)
         (* Current instruction is a type-checked instruction. *)
         (HTYCHECK: Ir.inst_typechecked md st1)
         (* Current instruction accesses memory
            from a guessed pointer. *)
         (HGUESSEDACCESS: memaccess_from_possibly_guessedptr md st1)
         (* It dereferences the twin block! *)
         (HDEREF: inst_derefs md st1 blkid = true),
    (* If step succeeds in st1, it fails in st2. *)
    forall e1' st1'
      (HSTEP1:Ir.SmallStep.sstep md st1 (Ir.SmallStep.sr_success e1' st1')),
          Ir.SmallStep.sstep md st2 Ir.SmallStep.sr_goes_wrong.
Proof.
  intros.
  unfold inst_derefs in HDEREF.
  inv HGUESSEDACCESS.
  { (* store. *)
    inv HSTEP1.
    { (* it was inst_step *)
      inv HISTEP; try congruence.
      rewrite <- HINST in HDEREF.
      dup HINST.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      apply Ir.SmallStep.ss_inst.
      apply Ir.SmallStep.s_det.
      rewrite twin_state_cur_inst_eq with (st2 := st2) (blkid := blkid) in HINST;
        try assumption.
      des_ifs; try (inv HTYCHECK; congruence).
      unfold Ir.SmallStep.inst_det_step.
      rewrite <- HINST.
      rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in Heq;
        try assumption.
      rewrite Heq.
      rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in Heq0;
        try assumption.
      rewrite Heq0.
      inv HGUESSED.
      inv HPHY. (* look at HDEREF: get_deref with phy suceeded. *)
      unfold Ir.deref in Heq1.
      (* now, high-level proof :deref from st2 should fail. *)
      des_ifs.
      dup Heq3. (* Let's make get_Deref st1 singleton. *)
      apply Ir.get_deref_phy_singleton in Heq3.
      { destruct Heq3; try congruence.
        destruct H. destruct H. inv H. destruct H0.
        destruct x. destruct p. simpl in H.  simpl in H0.
        (* Okay, now Heq4 says that deref succeeds. *)
        inv HDEREF. rewrite orb_false_r in H2. rewrite PeanoNat.Nat.eqb_eq in H2.
        subst b. (* and the deref in st1 is blkid. *)

        (* Now show that deref in st2 fails. *)
        apply twin_state_get_deref with (md := md) (st2 := st2) in Heq4;
          try eassumption; try congruence.
        unfold Ir.deref in Heq2. rewrite Heq4 in Heq2.
        (* false = true! *)
        congruence.
        eapply Ir.ty_bytesz_pos.
      }
      { inv HWF1. assumption. }
      { eapply Ir.ty_bytesz_pos. }
    }
    { (* store is not terminator *)
      apply Ir.Config.cur_inst_not_cur_terminator in HINST.
      unfold Ir.SmallStep.t_step in HTSTEP.
      rewrite <- HINST in HTSTEP. congruence.
    }
  }
  { (* load. *)
    inv HSTEP1.
    { (* it was inst_step *)
      inv HISTEP; try congruence.
      rewrite <- HINST in HDEREF.
      dup HINST.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      apply Ir.SmallStep.ss_inst.
      apply Ir.SmallStep.s_det.
      rewrite twin_state_cur_inst_eq with (st2 := st2) (blkid := blkid) in HINST;
        try assumption.
      des_ifs; try (inv HTYCHECK; congruence).
      unfold Ir.SmallStep.inst_det_step.
      rewrite <- HINST.
      rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in Heq;
        try assumption.
      rewrite Heq.
      inv HGUESSED.
      inv HPHY. (* look at HDEREF: get_deref with phy suceeded. *)
      unfold Ir.deref in Heq0.
      (* now, high-level proof :deref from st2 should fail. *)
      des_ifs.
      dup Heq2. (* Let's make get_Deref st1 singleton. *)
      apply Ir.get_deref_phy_singleton in Heq2.
      { destruct Heq2; try congruence.
        destruct H. destruct H. inv H. destruct H0.
        destruct x. destruct p. simpl in H.  simpl in H0.
        (* Okay, now Heq3 says that deref succeeds. *)
        inv HDEREF. rewrite orb_false_r in H2. rewrite PeanoNat.Nat.eqb_eq in H2.
        subst b. (* and the deref in st1 is blkid. *)

        (* Now show that deref in st2 fails. *)
        apply twin_state_get_deref with (md := md) (st2 := st2) in Heq3;
          try eassumption; try congruence.
        unfold Ir.deref in Heq1. rewrite Heq3 in Heq1.
        (* false = true! *)
        congruence.
        eapply Ir.ty_bytesz_pos.
      }
      { inv HWF1. assumption. }
      { eapply Ir.ty_bytesz_pos. }
    }
    { (* load is not terminator *)
      apply Ir.Config.cur_inst_not_cur_terminator in HINST.
      unfold Ir.SmallStep.t_step in HTSTEP.
      rewrite <- HINST in HTSTEP. congruence.
    }
  }
  { (* free. *)
    inv HSTEP1.
    { (* it was inst_step *)
      inv HISTEP; try congruence.
      rewrite <- HINST in HDEREF.
      dup HINST.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      apply Ir.SmallStep.ss_inst.
      apply Ir.SmallStep.s_det.
      rewrite twin_state_cur_inst_eq with (st2 := st2) (blkid := blkid) in HINST;
        try assumption.
      des_ifs; try (inv HTYCHECK; congruence).
      unfold Ir.SmallStep.inst_det_step.
      rewrite <- HINST.
      rewrite twin_state_get_val_eq with (st2 := st2) (blkid := blkid) in Heq;
        try assumption.
      rewrite Heq.
      inv HGUESSED.
      inv HPHY. (* look at HDEREF: get_deref with phy suceeded. *)
      des_ifs.
      unfold Ir.SmallStep.free in Heq0.
      unfold Ir.SmallStep.free in Heq1.
      des_ifs.
      unfold Ir.deref in Heq5.
      (* now, high-level proof :deref from st2 should fail. *)
      des_ifs.
      dup Heq6. (* Let's make get_Deref st1 singleton. *)
      apply Ir.get_deref_phy_singleton in Heq6.
      { destruct Heq6; try congruence.
        destruct H. destruct H. inv H. destruct H0.
        destruct x. destruct p. simpl in H.  simpl in H0.
        (* Okay, now Heq7 says that deref succeeds. *)
        inv HDEREF. rewrite orb_false_r in H2. rewrite PeanoNat.Nat.eqb_eq in H2.
        subst b1. (* and the deref in st1 is blkid. *)

        (* Now show that deref in st2 fails. *)
        apply twin_state_get_deref with (md := md) (st2 := st2) in Heq7;
          try eassumption; try congruence.
        unfold Ir.deref in Heq3. rewrite Heq7 in Heq3.
        (* false = true! *)
        congruence.
        omega.
      }
      { inv HWF1. assumption. }
      { omega. }
    }
    { (* free is not terminator *)
      apply Ir.Config.cur_inst_not_cur_terminator in HINST.
      unfold Ir.SmallStep.t_step in HTSTEP.
      rewrite <- HINST in HTSTEP. congruence.
    }
  }
Qed.      

End Ir.
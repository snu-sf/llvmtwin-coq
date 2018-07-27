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
Require Import SmallStepAux.

Module Ir.

Module SmallStep.

Import SmallStep.
Import Ir.
Import Ir.SmallStep.
Import SmallStepAux.
Import Ir.
Import Ir.SmallStep.

(****************************************************
        Theorems about sstep of instruction.
 ****************************************************)

Theorem incrpc_wf:
  forall md c c'
         (HWF:Ir.Config.wf md c)
         (HC':c' = incrpc md c),
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
      * simpl. intros.
        eapply wf_ptr. erewrite <- get_val_incrpc with (md := md).
        unfold incrpc. unfold Ir.Config.cur_fdef_pc. rewrite <- Heqs'.
        rewrite <- Heqofunid. rewrite <- Heqofdef'.
        rewrite <- Heqpc_next. unfold Ir.Config.update_pc.
        rewrite <- Heqs'. eassumption.
      * simpl. intros. eapply wf_ptr_mem.
        eassumption. eassumption. eassumption.
    + congruence.
  - congruence.
Qed.



Theorem update_rval_wf:
  forall md c c' r v
         (HWF:Ir.Config.wf md c)
         (HC':c' = Ir.Config.update_rval c r v)
         (HPTRWF:forall p, v = Ir.ptr p -> Ir.Config.ptr_wf p (Ir.Config.m c)),
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
      + eapply wf_ptr with (op := op). unfold Ir.Config.get_val. 
        des_ifs.
      + destruct (Nat.eqb r r0) eqn:Hreg.
        { apply HPTRWF with (p := p).
          rewrite Nat.eqb_eq in Hreg. subst r0.
          rewrite Ir.Regfile.get_update in HGETVAL. congruence. }
        { rewrite Nat.eqb_neq in Hreg.
          rewrite Ir.Regfile.get_update2 in HGETVAL; try congruence.
          eapply wf_ptr with (op := Ir.opreg r0).
          unfold Ir.Config.get_val. unfold Ir.Config.get_rval.
          des_ifs. }
  }
Qed.

Theorem update_reg_and_incrpc_wf:
  forall md c c' v r
         (HWF:Ir.Config.wf md c)
         (HC':c' = update_reg_and_incrpc md c r v)
         (HPTRWF:forall p, v = Ir.ptr p -> Ir.Config.ptr_wf p (Ir.Config.m c)),
    Ir.Config.wf md c'.
Proof.
  intros.
  unfold update_reg_and_incrpc in HC'.
  assert (Ir.Config.wf md (Ir.Config.update_rval c r v)).
  { eapply update_rval_wf. eassumption. reflexivity.  eassumption. }
  rewrite HC'.
  eapply incrpc_wf.
  eapply H. reflexivity.
Qed.


Theorem t_step_wf:
  forall md c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:t_step md c = sr_success e c'),
    Ir.Config.wf md c'.
Proof.
  intros.
  inv HWF.
  unfold t_step in HSTEP.
  des_ifs.
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq3. rewrite Heq3 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq5. rewrite Heq5 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq5. rewrite Heq5 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
Qed.




(****************************************************
   Theorems regarding categorization of instruction.
 ****************************************************)

Ltac thats_it := eapply update_reg_and_incrpc_wf; eauto.
Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).
Ltac try_wf :=
  des_ifs; try (eapply update_reg_and_incrpc_wf; try eassumption;
                try reflexivity; try congruence; fail).

Lemma no_mem_change_after_incrpc:
  forall md c,
    Ir.Config.m c = Ir.Config.m (incrpc md c).
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
  forall md c r v,
    Ir.Config.m c = Ir.Config.m (update_reg_and_incrpc md c r v).
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
  forall md c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HNEXT:Some (sr_success e c') = inst_det_step md c),
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
   changed after inst_step.
   This includes ptrtoint/inttoptr/psub/gep/icmp. *)
Theorem changes_mem_spec:
  forall md c i c' e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HSTEP:inst_step md c (sr_success e c')),
    c.(Ir.Config.m) = c'.(Ir.Config.m).
Proof.
  intros.
  inversion HSTEP.
  - eapply changes_mem_spec_det. eassumption.
    eassumption. assumption. eassumption.
  - (* malloc, NULL *)
    apply no_mem_change_after_update.
  - (* malloc *)
    rewrite <- HCUR in HCUR0. inversion HCUR0. rewrite H3 in HINST.
    rewrite HINST in HNOMEMCHG. inversion HNOMEMCHG.
  - (* iicmp_eq, nondet *) apply no_mem_change_after_update.
  - (* icmp_ule, nondet *) apply no_mem_change_after_update.
Qed.


End SmallStep.

End Ir.
Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Behaviors.

Module Ir.

Module Reordering.

(* Checks whether instruction i2 has data dependency on instruction i1.
   There's no data dependency, reordering 'i1;i2' into 'i2;i1' wouldn't break use-def chain.
   Note that this function does not check whether bi2 dominates i1.
   If i1 has no def (e.g. store instruction), this returns false. *)
Definition has_data_dependency (i1 i2:Ir.Inst.t): bool :=
  match (Ir.Inst.def i1) with
  | None => false
  | Some (r1, _) => (List.existsb (fun r => Nat.eqb r r1) (Ir.Inst.regops i2))
  end.
    
(* Analogous to Ir.SmallStep.incrpc, except that it returns None if there's no
   trivial next pc. *)
Definition incrpc' (md:Ir.IRModule.t) (c:Ir.Config.t):option Ir.Config.t :=
  match (Ir.Config.cur_fdef_pc md c) with
  | Some (fdef, pc0) =>
    match (Ir.IRFunction.next_trivial_pc pc0 fdef) with
    | Some pc' =>
      Some (Ir.Config.update_pc c pc')
    | None => None (* Cannot happen..! *)
    end
  | None => None (* Cannot happen *)
  end.

(* This proposition holds iff current pc points to i1,
   and the next pc points to i2. *)
Definition inst_locates_at (md:Ir.IRModule.t) (c:Ir.Config.t) (i1 i2:Ir.Inst.t):Prop :=
  exists c',
    Ir.Config.cur_inst md c = Some i1 /\
    Some c' = incrpc' md c /\
    Ir.Config.cur_inst md c' = Some i2.


(*****************************************************
        Lemmas about various functions
 *****************************************************)

Lemma incrpc_update_rval:
  forall md st r v,
    Ir.SmallStep.incrpc md (Ir.Config.update_rval st r v) =
    Ir.Config.update_rval (Ir.SmallStep.incrpc md st) r v.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
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
    Ir.Config.cur_inst md (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.cur_inst md (Ir.SmallStep.incrpc md st).
Proof.
  intros.
  unfold Ir.Config.cur_inst.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite incrpc_update_rval.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  reflexivity.
Qed.

Lemma incrpc'_incrpc:
  forall md st st'
         (HINCRPC':Some st' = incrpc' md st),
    st' = Ir.SmallStep.incrpc md st.
Proof.
  intros.
  unfold incrpc' in *.
  unfold Ir.SmallStep.incrpc.
  des_ifs.
Qed.

Lemma m_update_reg_and_incrpc:
  forall md st r v,
    Ir.Config.m (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.m st.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

Lemma m_incrpc:
  forall md st,
    Ir.Config.m (Ir.SmallStep.incrpc md st) =
    Ir.Config.m st.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

Lemma incrpc_update_reg_and_incrpc:
  forall md st r v,
    Ir.SmallStep.incrpc md (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.SmallStep.update_reg_and_incrpc md (Ir.SmallStep.incrpc md st) r v.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite incrpc_update_rval.
  reflexivity.
Qed.

Lemma get_val_incrpc:
  forall md st op,
    Ir.Config.get_val (Ir.SmallStep.incrpc md st) op = Ir.Config.get_val st op.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.get_val.
  des_ifs.
  unfold Ir.Config.update_pc.
  des_ifs.
  unfold Ir.Config.get_rval.
  simpl. rewrite Heq1. reflexivity.
Qed.

Lemma get_val_const_update_reg_and_incrpc:
  forall md st r v c,
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r v) (Ir.opconst c) =
    Ir.Config.get_val st (Ir.opconst c).
Proof.
  intros.
  unfold Ir.Config.get_val.
  des_ifs.
Qed.

Lemma get_val_independent:
  forall r1 r2 (HNEQ:r1 <> r2) md st v,
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r2 v) (Ir.opreg r1) =
    Ir.Config.get_val st (Ir.opreg r1).
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
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
  forall r2 opv md st v
         (HNEQ:opv <> Ir.opreg r2),
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r2 v) opv =
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
  forall st1 st2 md
         (HEQ:Ir.Config.eq_wopc st1 st2),
    Ir.Config.eq_wopc
      (Ir.SmallStep.incrpc md st1) st2.
Proof.
  intros.
  assert (HEQ_copy := HEQ).
  unfold Ir.Config.eq_wopc in HEQ.
  desH HEQ.
  split.
  - rewrite m_incrpc.
    assumption.
  - split.
    + unfold Ir.SmallStep.incrpc.
      des_ifs; unfold Ir.Config.update_pc.
      des_ifs.
      * inv HEQ0. rewrite Heq1. constructor.
      * inv HEQ0. simpl. simpl in H2. desH H2.
        destruct y. destruct p2.
        unfold Ir.Stack.eq_wopc. constructor.
        simpl in *. split. assumption. assumption.
        assumption.
    + split.
      * unfold Ir.SmallStep.incrpc.
        des_ifs.
        unfold Ir.Config.update_pc.
        des_ifs.
      * unfold Ir.SmallStep.incrpc.
        des_ifs.
        unfold Ir.Config.update_pc.
        des_ifs.
Qed.

Lemma update_rval_update_m:
  forall m st r v,
    Ir.Config.update_rval (Ir.Config.update_m st m) r v =
    Ir.Config.update_m (Ir.Config.update_rval st r v) m.
Proof.
  intros.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_m.
  simpl. des_ifs. rewrite Heq. reflexivity.
Qed.

Lemma get_funid_update_m:
  forall st m cid,
    Ir.Config.get_funid (Ir.Config.update_m st m) cid =
    Ir.Config.get_funid st cid.
Proof.
  intros.
  unfold Ir.Config.get_funid.
  unfold Ir.Config.update_m.
  simpl. reflexivity.
Qed.

Lemma cur_fdef_pc_update_m:
  forall m (md:Ir.IRModule.t) st,
    Ir.Config.cur_fdef_pc md (Ir.Config.update_m st m) =
    Ir.Config.cur_fdef_pc md st.
Proof.
  intros.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.update_m. simpl.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_m.
  simpl. des_ifs.
Qed.

Lemma update_pc_update_m:
  forall m st pc,
    Ir.Config.update_pc (Ir.Config.update_m st m) pc =
    Ir.Config.update_m (Ir.Config.update_pc st pc) m.
Proof.
  intros.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_m.
  simpl. des_ifs. rewrite Heq. reflexivity.
Qed.

Lemma eq_wopc_update_m:
  forall m st1 st2 (HEQ:Ir.Config.eq_wopc st1 st2),
    Ir.Config.eq_wopc (Ir.Config.update_m st1 m) (Ir.Config.update_m st2 m).
Proof.
  intros.
  inv HEQ.
  desH H0.
  split.
  - unfold Ir.Config.update_m. reflexivity.
  - split. assumption. split. assumption. assumption.
Qed.

Lemma incrpc_update_m:
  forall md st m,
         Ir.SmallStep.incrpc md (Ir.Config.update_m st m) =
         Ir.Config.update_m (Ir.SmallStep.incrpc md st) m.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  rewrite cur_fdef_pc_update_m.
  des_ifs. rewrite update_pc_update_m. reflexivity.
Qed.

Lemma m_update_m:
  forall st m,
    Ir.Config.m (Ir.Config.update_m st m) = m.
Proof.
  intros.
  unfold Ir.Config.update_m. reflexivity.
Qed.

Lemma update_reg_and_incrpc_update_m:
  forall st m md r v,
    Ir.SmallStep.update_reg_and_incrpc md (Ir.Config.update_m st m) r v=
    Ir.Config.update_m (Ir.SmallStep.update_reg_and_incrpc md st r v) m.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite update_rval_update_m.
  rewrite incrpc_update_m. reflexivity.
Qed.

Lemma cid_to_f_update_reg_and_incrpc:
  forall (st:Ir.Config.t) r v md,
    Ir.Config.cid_to_f (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.cid_to_f st.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.SmallStep.incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Lemma cid_fresh_update_reg_and_incrpc:
  forall (st:Ir.Config.t) r v md,
    Ir.Config.cid_fresh (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.cid_fresh st.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.SmallStep.incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.update_pc.
  des_ifs.
Qed.

Lemma stack_eq_wopc_update_pc1:
  forall st1 st2 pc1
         (HEQ:Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s st2)),
    Ir.Stack.eq_wopc (Ir.Config.s (Ir.Config.update_pc st1 pc1)) (Ir.Config.s st2).
Proof.
  intros.
  unfold Ir.Config.update_pc.
  inv HEQ.
  - rewrite <- H0. constructor.
  - desH H1.
    des_ifs.
    simpl. constructor.
    simpl. split; assumption. assumption.
Qed.

Lemma stack_eq_wopc_update_pc2:
  forall st1 st2 pc2
         (HEQ:Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s st2)),
    Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s (Ir.Config.update_pc st2 pc2)).
Proof.
  intros.
  unfold Ir.Config.update_pc.
  inv HEQ.
  - rewrite <- H. constructor.
  - desH H1.
    des_ifs.
    simpl. constructor.
    simpl. split; assumption. assumption.
Qed.

Lemma stack_eq_wopc_incrpc:
  forall st1 st2  md1 md2
         (HEQ:Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s st2)),
    Ir.Stack.eq_wopc (Ir.Config.s (Ir.SmallStep.incrpc md1 st1))
                     (Ir.Config.s (Ir.SmallStep.incrpc md2 st2)).
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  des_ifs.
  - apply stack_eq_wopc_update_pc1. apply stack_eq_wopc_update_pc2. assumption.
  - apply stack_eq_wopc_update_pc1. assumption.
  - apply stack_eq_wopc_update_pc1. assumption.
  - apply stack_eq_wopc_update_pc2. assumption.
  - apply stack_eq_wopc_update_pc2. assumption.
Qed.

Lemma config_eq_wopc_update_reg_and_incrpc_update_m_reorder:
  forall md1 md2 st r v m,
    Ir.Config.eq_wopc
      (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.Config.update_m st m) r v)
      (Ir.Config.update_m (Ir.SmallStep.update_reg_and_incrpc md2 st r v) m).
Proof.
  intros.
  split.
  - rewrite m_update_reg_and_incrpc.
    unfold Ir.Config.update_m. reflexivity.
  - split.
    {
      rewrite update_reg_and_incrpc_update_m.
      unfold Ir.Config.update_m. simpl.
      unfold Ir.SmallStep.update_reg_and_incrpc.
      apply stack_eq_wopc_incrpc. apply Ir.Stack.eq_wopc_refl.
    }
    { split. rewrite update_reg_and_incrpc_update_m. unfold Ir.Config.update_m. simpl.
      repeat (rewrite cid_to_f_update_reg_and_incrpc). reflexivity.
      rewrite update_reg_and_incrpc_update_m. unfold Ir.Config.update_m. simpl.
      repeat (rewrite cid_fresh_update_reg_and_incrpc). reflexivity. }
Qed.

Lemma config_eq_wopc_update_reg_and_incrpc_reorder:
  forall md1 md2 st r1 r2 v1 v2
         (HNEQ:r2 <> r1),
    Ir.Config.eq_wopc
      (Ir.SmallStep.update_reg_and_incrpc md1
        (Ir.SmallStep.update_reg_and_incrpc md1 st r1 v1) r2 v2)
      (Ir.SmallStep.update_reg_and_incrpc md2
        (Ir.SmallStep.update_reg_and_incrpc md2 st r2 v2) r1 v1).
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
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

Lemma cur_inst_update_rval:
  forall md st r v,
    Ir.Config.cur_inst md (Ir.Config.update_rval st r v) =
    Ir.Config.cur_inst md st.
Proof.
  intros.
  unfold Ir.Config.cur_inst.
  rewrite Ir.Config.cur_fdef_pc_update_rval. reflexivity.
Qed.

Lemma update_pc_update_rval:
  forall st r v p,
    Ir.Config.update_pc (Ir.Config.update_rval st r v) p =
    Ir.Config.update_rval (Ir.Config.update_pc st p) r v.
Proof.
  intros.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs; simpl in *.
  inv Heq1. inv Heq. reflexivity.
Qed.

Lemma update_pc_incrpc:
  forall md st p,
    Ir.Config.update_pc (Ir.SmallStep.incrpc md st) p =
    Ir.Config.update_pc st p.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.  
  unfold Ir.Config.update_pc.
  des_ifs; simpl in *.
  - rewrite Heq2 in Heq. congruence.
  - inv Heq.  reflexivity.
Qed.

Lemma cur_inst_update_m:
  forall md st m,
    Ir.Config.cur_inst md (Ir.Config.update_m st m) =
    Ir.Config.cur_inst md st.
Proof.
  intros.
  unfold Ir.Config.cur_inst.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.update_m.
  des_ifs.
Qed.

Lemma get_val_update_m:
  forall st m opv,
    Ir.Config.get_val (Ir.Config.update_m st m) opv =
    Ir.Config.get_val st opv.
Proof.
  intros.
  unfold Ir.Config.get_val.
  unfold Ir.Config.get_rval.
  unfold Ir.Config.update_m.
  simpl. reflexivity.
Qed.

Lemma get_val_update_reg_and_incrpc:
  forall md st r v o,
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r v) o =
    Ir.Config.get_val (Ir.Config.update_rval st r v) o.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite get_val_incrpc. reflexivity.
Qed.

Lemma inst_step_incrpc:
  forall md st e st' st2'
         (HINCR:Some st' = incrpc' md st)
         (HSTEP:Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success e st2')),
    Ir.Config.cur_inst md st' = Ir.Config.cur_inst md st2'.
Proof.
  intros.
  apply incrpc'_incrpc in HINCR.
  inv HSTEP;
    try (rewrite cur_inst_update_reg_and_incrpc; reflexivity).
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    des_ifs;
      try(rewrite cur_inst_update_reg_and_incrpc; reflexivity);
      try(rewrite incrpc_update_m; rewrite cur_inst_update_m; reflexivity).
  - rewrite cur_inst_update_reg_and_incrpc.
    rewrite incrpc_update_m.
    rewrite cur_inst_update_m.
    reflexivity.
Qed.

(****************************************
  Lemmas about Ir.SmallStep.inst_step
 ****************************************)

(* If instruction i does not allocate  memory, it does not raise OOM. *)
Lemma no_alloc_no_oom:
  forall i st md
         (HNOMEMCHG:Ir.SmallStep.allocates_mem i = false)
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HOOM:Ir.SmallStep.inst_step md st Ir.SmallStep.sr_oom),
    False.
Proof.
  intros.
  inversion HOOM.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HINST in HNEXT.
    destruct i; des_ifs.
  - rewrite HINST in HCUR.
    inversion HCUR. rewrite HINST0 in H1.
    rewrite <- H1 in HNOMEMCHG. inversion HNOMEMCHG.
Qed.

Lemma never_goes_wrong_no_gw:
  forall i st md
         (HNOMEMCHG:Ir.SmallStep.never_goes_wrong i = true)
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HGW:Ir.SmallStep.inst_step md st Ir.SmallStep.sr_goes_wrong),
    False.
Proof.
  intros.
  inv HGW.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  des_ifs.
Qed.
 
(* If instruction i does not finish program.
 (note that ret is terminator) *)
Lemma inst_no_prog_finish:
  forall i st md v
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HOOM:Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_prog_finish v)),
    False.
Proof.
  intros.
  inversion HOOM.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HINST in HNEXT.
    destruct i; des_ifs.
Qed.

(* If instruction i does not allocate memory, it either goes wrong
   or succeed. *)
Lemma no_alloc_goes_wrong_or_success:
  forall i st md sr
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HNOALLOC:Ir.SmallStep.allocates_mem i = false)
         (HNEXT:Ir.SmallStep.inst_step md st sr),
    (sr = Ir.SmallStep.sr_goes_wrong \/
     exists e st', sr = Ir.SmallStep.sr_success e st').
Proof.
  intros.
  inv HNEXT;
  try (rewrite <- HCUR in HINST;
    inv HINST; simpl in HNOALLOC; congruence);
  try (right; eexists; eexists; reflexivity).
  unfold Ir.SmallStep.inst_det_step in HNEXT0.
  rewrite HINST in HNEXT0.
  des_ifs;
  try (left; reflexivity);
  try (right; eexists; eexists; reflexivity).
Qed.


(***************************************************
  Definition of equivalence of inst_nstep results
 **************************************************)

Inductive nstep_eq: (Ir.trace * Ir.SmallStep.step_res) ->
                    (Ir.trace * Ir.SmallStep.step_res) -> Prop :=
| nseq_goes_wrong:
    forall (t1 t2:Ir.trace)
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_goes_wrong)) (t2, (Ir.SmallStep.sr_goes_wrong))
| nseq_oom:
    forall (t1 t2:Ir.trace)
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_oom)) (t2, (Ir.SmallStep.sr_oom))
| nseq_prog_finish:
    forall (t1 t2:Ir.trace) v
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_prog_finish v)) (t2, (Ir.SmallStep.sr_prog_finish v))
| nseq_success:
    forall (t1 t2:Ir.trace) e c1 c2
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2)
        (HCEQ:Ir.Config.eq_wopc c1 c2),
      nstep_eq (t1, (Ir.SmallStep.sr_success e c1))
               (t2, (Ir.SmallStep.sr_success e c2)).

Lemma nstep_eq_refl:
  forall sr, nstep_eq sr sr.
Proof.
  destruct sr.
  destruct s.
  - constructor. reflexivity. apply Ir.Config.eq_wopc_refl.
  - constructor. reflexivity.
  - constructor. reflexivity.
  - constructor. reflexivity.
Qed.

(* This lemma is valid because eq_wopc does not compare PCs. *)
Lemma nstep_eq_trans_1:
  forall tr e md1 md2 sr' st r1 v1 r2 v2
         (HNEQ:r1 <> r2),
    nstep_eq (tr, Ir.SmallStep.sr_success e
            (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.SmallStep.update_reg_and_incrpc md1 st r1 v1) r2 v2))
                       sr'
    <->
    nstep_eq (tr, Ir.SmallStep.sr_success e
            (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.SmallStep.update_reg_and_incrpc md2 st r2 v2) r1 v1))
                       sr'.
Proof.
  intros.
  split.
  { intros HEQ.
    inv HEQ.
    constructor.
    assumption.
    assert (Ir.Config.eq_wopc
              (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.SmallStep.update_reg_and_incrpc md2 st r2 v2) r1 v1)
              (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.SmallStep.update_reg_and_incrpc md1 st r1 v1) r2 v2)).
    { apply config_eq_wopc_update_reg_and_incrpc_reorder. assumption. }
    eapply Ir.Config.eq_wopc_trans.
    eassumption.
    eassumption.
  }
  { intros HEQ.
    inv HEQ.
    constructor.
    assumption.
    assert (Ir.Config.eq_wopc
              (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.SmallStep.update_reg_and_incrpc md1 st r1 v1) r2 v2)
              (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.SmallStep.update_reg_and_incrpc md2 st r2 v2) r1 v1)).
    { apply config_eq_wopc_update_reg_and_incrpc_reorder.
      apply not_eq_sym. assumption. }
    eapply Ir.Config.eq_wopc_trans.
    eassumption.
    eassumption.
  }
Qed.

(* This lemma is valid because eq_wopc does not compare PCs. *)
Lemma nstep_eq_trans_2:
  forall tr e md1 md2 sr' st r1 v1 r2 v2 m
         (HNEQ:r1 <> r2),
    nstep_eq (tr, Ir.SmallStep.sr_success e
            (Ir.SmallStep.update_reg_and_incrpc md1
               (Ir.Config.update_m (Ir.SmallStep.update_reg_and_incrpc md1 st r1 v1) m) r2 v2)) sr'
    <->
    nstep_eq (tr, Ir.SmallStep.sr_success e
              (Ir.SmallStep.update_reg_and_incrpc md2
                 (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.Config.update_m st m) r2 v2) r1 v1))
                       sr'.
Proof.
  intros.
  split.
  { intros HEQ.
    inv HEQ.
    constructor.
    assumption.
    rewrite <- update_reg_and_incrpc_update_m in HCEQ.
    assert (Ir.Config.eq_wopc
              (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.Config.update_m st m) r2 v2) r1 v1)
              (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.Config.update_m st m) r1 v1) r2 v2)).
    { eapply config_eq_wopc_update_reg_and_incrpc_reorder. assumption. }
    eapply Ir.Config.eq_wopc_trans.
    eassumption.
    eassumption.
  }
  { intros HEQ.
    inv HEQ.
    constructor.
    assumption.
    rewrite <- update_reg_and_incrpc_update_m.
    assert (Ir.Config.eq_wopc
              (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.SmallStep.update_reg_and_incrpc md2 (Ir.Config.update_m st m) r2 v2) r1 v1)
              (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.SmallStep.update_reg_and_incrpc md1 (Ir.Config.update_m st m) r1 v1) r2 v2)).
    { eapply config_eq_wopc_update_reg_and_incrpc_reorder. assumption. }
    apply Ir.Config.eq_wopc_symm in H.
    eapply Ir.Config.eq_wopc_trans.
    eassumption.
    eassumption.
  }
Qed.

Lemma nstep_eq_trans_3:
  forall tr e md1 md2 sr' st r v m,
    nstep_eq (tr, Ir.SmallStep.sr_success e
            (Ir.SmallStep.update_reg_and_incrpc md1
               (Ir.Config.update_m (Ir.SmallStep.incrpc md1 st) m) r v)) sr'
    <->
    nstep_eq (tr, Ir.SmallStep.sr_success e
            (Ir.SmallStep.incrpc md2
              (Ir.Config.update_m
                (Ir.SmallStep.update_reg_and_incrpc md2 st r v) m))) sr'.
Proof.
  intros.
  split.
  { intros H.
    inv H.
    constructor.
    assumption.
    rewrite <- update_reg_and_incrpc_update_m.
    rewrite incrpc_update_reg_and_incrpc.
    rewrite incrpc_update_m.
    apply Ir.Config.eq_wopc_trans with (c2 := (Ir.SmallStep.update_reg_and_incrpc md1
              (Ir.Config.update_m (Ir.SmallStep.incrpc md1 st) m) r v));
      try assumption.
    unfold Ir.SmallStep.update_reg_and_incrpc.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_symm.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_update_rval.
    apply eq_wopc_update_m.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_symm.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_refl.
  }
  { intros H.
    inv H.
    constructor.
    assumption.
    rewrite update_reg_and_incrpc_update_m.
    rewrite <- incrpc_update_reg_and_incrpc.
    rewrite <- incrpc_update_m.
    apply Ir.Config.eq_wopc_trans with
        (c2 := (Ir.SmallStep.incrpc md2
              (Ir.Config.update_m (Ir.SmallStep.update_reg_and_incrpc md2 st r v) m)));
      try assumption.
    unfold Ir.SmallStep.update_reg_and_incrpc.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_symm.
    apply config_eq_wopc_incrpc.
    apply eq_wopc_update_m.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_symm.
    apply config_eq_wopc_incrpc.
    apply Ir.Config.eq_wopc_update_rval.
    apply Ir.Config.eq_wopc_refl.
  }
Qed.

(***************************************************
        Definition of valid reordering.
 **************************************************)

(* Is it valid to reorder 'i1;i2' into 'i2;i1'? *)
Definition inst_reordering_valid (i1 i2:Ir.Inst.t): Prop :=
  forall
    (* If there's no data dependency from i1 to i2 *)
    (HNODEP:has_data_dependency i1 i2 = false),
    (* 'i1;i2' -> 'i2;i1' is allowed *)
    forall (md md':Ir.IRModule.t) (* IR Modules *)
           (sr:Ir.trace * Ir.SmallStep.step_res)
           (st:Ir.Config.t) (* Initial state *)
           (HWF:Ir.Config.wf md st) (* Well-formedness of st *)
           (HLOCATE:inst_locates_at md st i1 i2)
           (HLOCATE':inst_locates_at md' st i2 i1)
           (HSTEP:Ir.SmallStep.inst_nstep md st 2 sr),
      exists sr', (* step result after 'i2;i1' *)
        Ir.SmallStep.inst_nstep md' st 2 sr' /\
        nstep_eq sr sr'.


Ltac do_nseq_refl :=
  apply nseq_success; try reflexivity; apply Ir.Config.eq_wopc_refl.



(********************************************
   REORDERING of malloc - ptrtoint:

   r1 = malloc ty opptr1
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2
   r1 = malloc ty opptr1.
**********************************************)

Theorem reorder_malloc_ptrtoint:
  forall i1 i2 r1 r2 opptr1 opptr2 ty1 ty2
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 ty2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - inv HSUCC; try (inv HSUCC0; fail).
    (* Okay, inst1(malloc) succeeded. *) 
    assert (HLOCATE1'':Ir.Config.cur_inst md c' = Some (Ir.Inst.iptrtoint r2 opptr2 ty2)).
    {
      rewrite <- inst_step_incrpc with (st := st) (e := e) (st' := Ir.SmallStep.incrpc md st).
      apply incrpc'_incrpc in HLOCATE_NEXT. rewrite HLOCATE_NEXT in HLOCATE2. assumption.
      rewrite <- HLOCATE_NEXT. apply incrpc'_incrpc in HLOCATE_NEXT. congruence.
      assumption. }
    inv HSINGLE; try congruence.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HLOCATE1'' in HNEXT. inv HNEXT.
    (* Okay, now - how did malloc succeed? *)
    inv HSINGLE0; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence. }
    + (* Malloc returned NULL. *)
      rewrite HLOCATE1 in HCUR. inv HCUR.
      eexists.
      split.
      * eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        (* okay, execute ptrtoint first, in target. *)
        eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite HLOCATE1'.  reflexivity.
        (* and, run malloc. *)
        eapply Ir.SmallStep.s_malloc_zero. rewrite cur_inst_update_reg_and_incrpc.
        apply incrpc'_incrpc in HLOCATE_NEXT'. rewrite HLOCATE_NEXT' in HLOCATE2'. rewrite HLOCATE2'. reflexivity.
        reflexivity.
        destruct opptr1. rewrite get_val_const_update_reg_and_incrpc. assumption.
        rewrite get_val_independent. assumption. 
        admit. (* Impossible syntax *)
      * rewrite nstep_eq_trans_1. apply nseq_success. reflexivity.
        destruct opptr2. rewrite get_val_const_update_reg_and_incrpc. rewrite m_update_reg_and_incrpc.
        apply Ir.Config.eq_wopc_refl.
        rewrite get_val_independent.  rewrite m_update_reg_and_incrpc.
        apply Ir.Config.eq_wopc_refl.
        admit. (* SSa *)
        admit. (* HNODEP *)
    + (* malloc succeeded. *)
      rewrite HLOCATE1 in HCUR. inv HCUR.
      rewrite m_update_reg_and_incrpc.
      eexists.
      split.
      * eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        (* okay, execute ptrtoint first, in target. *)
        eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite HLOCATE1'.  reflexivity.
        (* and, run malloc. *)
        eapply Ir.SmallStep.s_malloc. rewrite cur_inst_update_reg_and_incrpc.
        apply incrpc'_incrpc in HLOCATE_NEXT'. rewrite HLOCATE_NEXT' in HLOCATE2'. rewrite HLOCATE2'. reflexivity.
        reflexivity.
        destruct opptr1. rewrite get_val_const_update_reg_and_incrpc. eassumption.
        rewrite get_val_independent. assumption. 
        admit. (* Impossible *)
        assumption.
        reflexivity. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
      * eapply nstep_eq_trans_2 with (md1 := md').
        admit. (* SSA *)
        rewrite update_reg_and_incrpc_update_m with (m := m') (md := md).
        rewrite get_val_update_m.
        (* now we should show that opptr2 isn't something like (l, ofs).
           Note that l is a new block id. *)
        inv HWF.
        (* opptr2 (which is operand of ptrtoint) cannot be log (l, 0). *)
        destruct opptr2.
        -- rewrite get_val_const_update_reg_and_incrpc.
           destruct (Ir.Config.get_val st (Ir.opconst c)) eqn:Hopc.
           { destruct v; try do_nseq_refl.
             - destruct p.
               + destruct p. admit. (* about logical pointer *)
               + unfold Ir.SmallStep.p2N. do_nseq_refl.
           }
           { do_nseq_refl. }
        -- rewrite get_val_independent.
           destruct (Ir.Config.get_val st (Ir.opreg r)) eqn:Hopr.
           { destruct v; try do_nseq_refl.
             - destruct p.
               + destruct p. admit. (* about logical pointer. *)
               + unfold Ir.SmallStep.p2N. do_nseq_refl.
           }
           { do_nseq_refl. }
           admit. (* r <> r1 *)
  - (* malloc raised oom. *)
    inv HOOM.
    inv HSINGLE.
    + unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence.
    + eexists. split.
      eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step.
      rewrite HLOCATE1'. reflexivity.
      eapply Ir.SmallStep.s_malloc_oom.
      rewrite cur_inst_update_reg_and_incrpc.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      rewrite HLOCATE2'. reflexivity. reflexivity.
      rewrite HLOCATE1 in HCUR. inv HCUR.
      destruct opptr1.
      * rewrite get_val_const_update_reg_and_incrpc. eassumption.
      * rewrite get_val_independent. assumption.
        admit. (* r <> r2 *)
      * rewrite m_update_reg_and_incrpc. assumption.
      * constructor. reflexivity.
    + inv HSUCC.
    + inv HOOM0.
  - (* malloc raised goes_wrong - impossible *)
    inv HGW.
    + inv HSINGLE.
      unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence.
    + inv HSUCC.
    + inv HGW0.
Admitted.




(********************************************
   REORDERING of ptrtoint - malloc:

   r1 = ptrtoint opptr1 ty1
   r2 = malloc ty2 opptr2
   ->
   r2 = malloc ty2 opptr2
   r1 = ptrtoint opptr1 ty1
**********************************************)

Theorem reorder_ptrtoint_malloc:
  forall i1 i2 r1 r2 opptr1 opptr2 ty1 ty2
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 ty1)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* ptrtoint succeed - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc(0) *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      eexists. split.
      {
        eapply Ir.SmallStep.ns_success.
        {
          eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_malloc_zero.
          rewrite HLOCATE1'. reflexivity. reflexivity.
          rewrite get_val_independent2 in HZERO. assumption.
          destruct opptr2. intro H. inversion H.
          assert (r <> r1). admit.
          intros H0. inv H0. congruence.
        }
        { (* ptrtoint in md' *)
          eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite cur_inst_update_reg_and_incrpc.
          apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite HLOCATE2'. reflexivity.
        }
      }
      {
        rewrite m_update_reg_and_incrpc.
        rewrite nstep_eq_trans_1 with (md2 := md').
        rewrite get_val_independent2.
        apply nstep_eq_refl.
        destruct opptr1. intros H. congruence.
        assert (r <> r2). admit.
        intros H1. congruence.
        assert (r1 <> r2). admit. congruence.
      }
    + (* oom *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      eexists (nil, Ir.SmallStep.sr_oom).
      split.
      { eapply Ir.SmallStep.ns_oom.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc_oom.
        rewrite HLOCATE1'. reflexivity. reflexivity.
        rewrite get_val_independent2 in HSZ. eassumption.
        destruct opptr2. intros H. congruence.
        intros H2.
        assert (r <> r1). admit.
        congruence.
        rewrite m_update_reg_and_incrpc in HNOSPACE. assumption.
      }
      { constructor. reflexivity. }
    + (* malloc succeeds *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      rewrite m_update_reg_and_incrpc in *.
      rewrite cur_inst_update_reg_and_incrpc in *.
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc. rewrite HLOCATE1'. reflexivity. reflexivity.
        rewrite get_val_independent2 in HSZ. eassumption.
        destruct opptr2. intros H. congruence.
        assert(r <> r1). admit.
        intros H2. congruence.
        assumption. reflexivity. eassumption. eassumption.
        eassumption.
        eapply Ir.SmallStep.s_det.
        unfold Ir.SmallStep.inst_det_step.
        rewrite cur_inst_update_reg_and_incrpc.
        rewrite incrpc_update_m.
        rewrite cur_inst_update_m.
        apply incrpc'_incrpc in HLOCATE_NEXT'.
        rewrite HLOCATE_NEXT' in HLOCATE2'.
        rewrite HLOCATE2'. reflexivity.
      }
      { eapply nstep_eq_trans_2 with (md2 := md').
        assert (r1 <> r2). admit. assumption.
        rewrite get_val_independent2.
        rewrite get_val_update_m.
        rewrite m_update_reg_and_incrpc.
        destruct (Ir.Config.get_val st opptr1) eqn:Hopptr1; try apply nstep_eq_refl.
        destruct v; try apply nstep_eq_refl.
        admit. (* p2N does not change even if malloc is called *)
        destruct opptr1. intros H. congruence.
        assert (r <> r2). admit.
        intros. congruence.
      }
  - (* ptrtoint never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iptrtoint r1 opptr1 ty1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* ptrtoint never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iptrtoint r1 opptr1 ty1)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of free - ptrtoint:

   free opptr1
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2
   free opptr1
**********************************************)

Theorem reorder_free_ptrtoint:
  forall i1 i2 r2 opptr1 (opptr2:Ir.op) retty2
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 retty2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* free succeed *)
    inv HSUCC; try (inv HSUCC0; fail).
    inv HSINGLE0; try congruence.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HLOCATE1 in HNEXT.
    des_ifs.
    inv HSINGLE; try
      (rewrite incrpc_update_m in HCUR; rewrite cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    rewrite incrpc_update_m in HNEXT.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite cur_inst_update_m in HNEXT.
    apply incrpc'_incrpc in HLOCATE_NEXT.
    rewrite HLOCATE_NEXT in HLOCATE2.
    rewrite HLOCATE2 in HNEXT.
    inv HNEXT.
    eexists. split.
    { eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step.
      rewrite HLOCATE1'.
      reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step.
      rewrite cur_inst_update_reg_and_incrpc.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      rewrite HLOCATE2'.
      rewrite get_val_independent2.
      rewrite m_update_reg_and_incrpc.
      rewrite Heq.
      rewrite Heq0.
      reflexivity.
      destruct opptr1. intros H0. congruence.
      assert (r <> r2). admit. congruence.
    }
    { rewrite get_val_update_m.
      rewrite get_val_incrpc.
      rewrite nstep_eq_trans_3 with (md2 := md').
      destruct retty2.
      - destruct (Ir.Config.get_val st opptr2) eqn:Hopptr2.
        + destruct v;try apply nstep_eq_refl.
          admit. (* p2N does not change after free *)
        + apply nstep_eq_refl.
      - apply nstep_eq_refl.
    }
  - (* free never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.ifree opptr1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* free goes wrong. *)
    inv HGW.
    + inv HSINGLE; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT.
      eexists.
      split.
      { eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_det.
        unfold Ir.SmallStep.inst_det_step.
        rewrite HLOCATE1'.
        reflexivity.
        eapply Ir.SmallStep.s_det.
        apply incrpc'_incrpc in HLOCATE_NEXT'.
        rewrite HLOCATE_NEXT' in HLOCATE2'.
        unfold Ir.SmallStep.inst_det_step.
        rewrite cur_inst_update_reg_and_incrpc.
        rewrite HLOCATE2'.
        rewrite get_val_independent2.
        rewrite m_update_reg_and_incrpc.
        des_ifs.
        destruct opptr1. intros H0. congruence.
        assert (r <> r2). admit. congruence.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of ptrtoint - free:

   r1 = ptrtoint opptr1 ty1
   free opptr2
   ->
   free opptr2
   r1 = ptrtoint opptr1 ty1
**********************************************)

Ltac unfold_det HNEXT HLOCATE :=
    unfold Ir.SmallStep.inst_det_step in HNEXT;
    try rewrite cur_inst_update_reg_and_incrpc in HNEXT; 
    rewrite HLOCATE in HNEXT.


Theorem reorder_ptrtoint_free:
  forall i1 i2 r1 opptr1 (opptr2:Ir.op) retty1
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 retty1)
         (HINST2:i2 = Ir.Inst.ifree opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  apply incrpc'_incrpc in HLOCATE_NEXT.
  apply incrpc'_incrpc in HLOCATE_NEXT'.
  rewrite HLOCATE_NEXT in HLOCATE2.
  rewrite HLOCATE_NEXT' in HLOCATE2'.
  inv HSTEP.
  - inv HSUCC; try (inv HSUCC0; fail).
    inv HSINGLE0; try congruence.
    unfold_det HNEXT HLOCATE1. inv HNEXT.
    inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                      rewrite HLOCATE2 in HCUR; congruence).
    unfold_det HNEXT HLOCATE2.
    rewrite m_update_reg_and_incrpc in HNEXT.
    rewrite get_val_independent2 in HNEXT.
    des_ifs; try (
      eexists; split;
      [
        eapply Ir.SmallStep.ns_success;
        [
          eapply Ir.SmallStep.ns_one;
          eapply Ir.SmallStep.s_det;
          unfold Ir.SmallStep.inst_det_step;
          rewrite HLOCATE1';
          rewrite Heq; rewrite Heq0; reflexivity
        |
          eapply Ir.SmallStep.s_det;
          unfold Ir.SmallStep.inst_det_step; rewrite incrpc_update_m;
          rewrite cur_inst_update_m; rewrite HLOCATE2';
          reflexivity
        ]
      |
        rewrite get_val_update_m; rewrite get_val_incrpc; rewrite Heq1;
        rewrite <- nstep_eq_trans_3 with (md1 := md');
        apply nstep_eq_refl
      ]; fail).
    + eexists. split. eapply Ir.SmallStep.ns_goes_wrong.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. reflexivity.
      constructor. reflexivity.
    + eexists. split.
      { eapply Ir.SmallStep.ns_success.
        { eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
          rewrite Heq. rewrite Heq0. reflexivity.
        }
        { eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
          rewrite cur_inst_update_m. rewrite HLOCATE2'.
          reflexivity. }
      }
      { rewrite get_val_update_m. rewrite get_val_incrpc. rewrite Heq1.
        rewrite <- nstep_eq_trans_3 with (md1 := md').
        rewrite m_update_m.
        admit. (* p2N after free is the same *) }
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite cur_inst_update_m. rewrite HLOCATE2'.
      reflexivity.
      rewrite <- nstep_eq_trans_3 with (md1 := md').
      apply nstep_eq_refl.
    + eexists. split. eapply Ir.SmallStep.ns_goes_wrong.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      constructor. reflexivity.
    + eexists. split. eapply Ir.SmallStep.ns_goes_wrong.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. reflexivity.
      constructor. reflexivity.
    + eexists. split. eapply Ir.SmallStep.ns_goes_wrong.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. reflexivity.
      constructor. reflexivity.
    + destruct opptr2. intros H0. congruence.
      assert (r <> r1). admit. congruence.
  - (* ptrtoint never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iptrtoint r1 opptr1 retty1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* ptrtoint never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iptrtoint r1 opptr1 retty1)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.

End Reordering.

End Ir.
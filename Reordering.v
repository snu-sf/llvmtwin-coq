Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.

Require Import Common.
Require Import Lang.
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

Lemma incrpc_update_m:
  forall m md st,
    Ir.SmallStep.incrpc md (Ir.Config.update_m st m) =
    Ir.Config.update_m (Ir.SmallStep.incrpc md st) m.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.update_m.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.get_funid.
  des_ifs; simpl in *;
    try (inv Heq1; congruence).
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

Lemma get_val_const_update_reg_and_incrpc:
  forall md st r v c,
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r v) (Ir.opconst c) =
    Ir.Config.get_val st (Ir.opconst c).
Proof.
  intros.
  unfold Ir.Config.get_val.
  des_ifs.
Qed.


(* Is it valid to reorder 'i1;i2' into 'i2;i1'? *)
Definition inst_reordering_valid (i1 i2:Ir.Inst.t): Prop :=
  (* If there's no data dependency from i1 to i2 *)
  forall (HNODEP:has_data_dependency i1 i2 = false),
    (* 'i1;i2' -> 'i2;i1' is allowed *)
    forall (md md':Ir.IRModule.t) (* IR Modules *)
           (sr:Ir.trace * Ir.SmallStep.step_res)
           (st:Ir.Config.t) (* Initial state *)
           (HWF:Ir.Config.wf md st) (* Well-formedness of st *)
           (HLOCATE:inst_locates_at md st i1 i2)
           (HLOCATE':inst_locates_at md' st i2 i1)
           (HSTEP:Ir.SmallStep.inst_nstep md st 2 sr),
      exists sr', (* step result after 'i2;i1' *)
        nstep_eq sr sr' /\
        Ir.SmallStep.inst_nstep md' st 2 sr'.


(* Reordering between ptrtoint/ptrtoint:

   r1 = ptrtoint opptr1 ty1;
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2;
   r1 = ptrtoint opptr1 ty1
*)

Lemma ptrtoint_success:
  forall md e st st' r opv retty
         (HINST:Some (Ir.Inst.iptrtoint r opv retty) = Ir.Config.cur_inst md st)
         (HSUCCESS:Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success e st')),
    exists v, st' = Ir.SmallStep.update_reg_and_incrpc md st r v.
Proof.
  intros.
  inv HSUCCESS; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite <- HINST in HNEXT.
  des_ifs; eexists; reflexivity.
Qed.

Lemma ptrtoint_const_independent:
  forall i1 i2 r1 oc ty1
         (HINST:i1 = Ir.Inst.iptrtoint r1 (Ir.opconst oc) ty1),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.

(* Lemma no_alloc_goes_wrong_or_success:
  forall i st md sr
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HNOALLOC:Ir.SmallStep.allocates_mem i = false)
         (HNEXT:Ir.SmallStep.inst_step md st sr),
    (sr = Ir.SmallStep.sr_goes_wrong \/
     exists e st', sr = Ir.SmallStep.sr_success e st').*)

  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  admit.
  - (* ptrtoint cannot raise OOM. *) inv HOOM.
    inv HSINGLE; try congruence. unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HLOCATE1 in HNEXT. des_ifs.
    inv HSUCC. inv HOOM0.
  - 
 
         (HST:st' = Ir.SmallStep.update_reg_and_incrpc md st r v)
         (HINST:Some (Ir.Inst.iptrtoint r' (Ir.opconst c') retty') = Ir.Config.cur_inst md st')
         (HSUCCESS:Ir.SmallStep.inst_step md st' (Ir.SmallStep.sr_success e st'')),
    exists v', st' = Ir.SmallStep.update_reg_and_incrpc md st r v'.
Proof.
  intros.
  inv HSUCCESS; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite <- HINST in HNEXT.
  des_ifs; eexists; reflexivity.
Qed.


Lemma reorder_ptrtoint_ptrtoint:
  forall i1 i2 r1 r2 opptr1 opptr2 ty1 ty2
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 ty1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 ty2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  assert (HNOMEMCHG1:Ir.SmallStep.changes_mem i1 = false).
  { rewrite HINST1. reflexivity. }
  assert (HNOMEMCHG2:Ir.SmallStep.changes_mem i2 = false).
  { rewrite HINST2. reflexivity. }

  unfold inst_reordering_valid.
  intros.
  unfold has_data_dependency in HNODEP.
  rewrite HINST1, HINST2 in HNODEP.
  unfold Ir.Inst.regops in HNODEP.
  unfold Ir.regop in HNODEP.
  simpl in HNODEP.

  unfold inst_locates_at in *.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - inv HSUCC.
    + assert (HLOCATE1R:Ir.Config.cur_inst md c' = Some (Ir.Inst.iptrtoint r2 opptr2 ty2)).
      { rewrite <- HLOCATE2. symmetry. eapply inst_step_incrpc.
        eassumption. eassumption. }
      inv HSINGLE; try congruence.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1R in HNEXT.
      destruct ty2; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite HLOCATE1 in HNEXT0.
      destruct ty1; try congruence.
      apply incrpc'_incrpc in HLOCATE_NEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      destruct sr0.
      * (* Success, after first instruction. *)
        destruct (Ir.Config.get_val st opptr1) eqn:HOPPTR1; try congruence.
        destruct v eqn:Hv; try congruence; inv HNEXT0.
        { destruct opptr2.
          - (* opptr2 is constant. *)
            rewrite get_val_const_update_reg_and_incrpc in HNEXT.
            destruct (Ir.Config.get_val st (Ir.opconst c)) eqn:HOPC2; try congruence.
            destruct v eqn:Hv2; try congruence.
            + rewrite m_update_reg_and_incrpc in *.
              inv HNEXT.
              
        rewrite get_val_independent in HNEXT.
      * (* Success, Success. *)
        
        (* opptr1 may be constant. *)
        destruct opptr1.
        { des_ifs.
          { eexists.
            
        des_ifs.
        { simpl in HNODEP.
          rewrite m_update_reg_and_incrpc.
          eexists.
          rewrite nstep_eq_trans_1 with (md2 := md').
          split. apply nstep_eq_refl.
          eapply Ir.SmallStep.ns_success.
          eapply Ir.SmallStep.ns_one.
          constructor. unfold Ir.SmallStep.inst_det_step.
          rewrite HLOCATE1'. rewrite get_val_const_update_reg_and_incrpc in Heq0.
          rewrite Heq0. reflexivity.
          constructor. unfold Ir.SmallStep.inst_det_step.
          rewrite cur_inst_update_reg_and_incrpc.
          rewrite HLOCATE2'.
          destruct opptr1.
          - rewrite get_val_const_update_reg_and_incrpc.
            rewrite Heq. rewrite m_update_reg_and_incrpc. reflexivity.
          - rewrite get_val_independent. rewrite Heq.
            rewrite m_update_reg_and_incrpc. reflexivity.
            admit. (* USE-DEF *)
          - admit. (* SSA *)
        }
        { simpl in HNODEP. rewrite orb_false_r in HNODEP. rewrite PeanoNat.Nat.eqb_neq in HNODEP.
          rewrite m_update_reg_and_incrpc.
          eexists.
          rewrite nstep_eq_trans_1 with (md2 := md').
          split. apply nstep_eq_refl.
          eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
          constructor. unfold Ir.SmallStep.inst_det_step.
          rewrite HLOCATE1'.
          rewrite get_val_independent in Heq0 by assumption. rewrite Heq0. reflexivity.
          constructor. unfold Ir.SmallStep.inst_det_step.
          rewrite cur_inst_update_reg_and_incrpc.
          rewrite HLOCATE2'.
          destruct opptr1.
          - rewrite get_val_const_update_reg_and_incrpc.
            rewrite Heq. rewrite m_update_reg_and_incrpc. reflexivity.
          - rewrite get_val_independent. rewrite Heq.
            rewrite m_update_reg_and_incrpc. reflexivity.
            admit. (* USE-DEF *)
          - admit. (* SSA *)
        }
        { simpl in HNODEP.
          rewritre 
          rewrite update_reg_and_incrpc_independent.
    + inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT.
      des_ifs.
      * inv HSINGLE.
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in *.
        apply incrpc'_incrpc in HLOCATE_NEXT.
        rewrite <- HLOCATE_NEXT in HNEXT.
        rewrite HLOCATE2 in HNEXT.
        des_ifs.
        
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in *;
           apply incrpc'_incrpc in HLOCATE_NEXT;
           congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in *.
        assert (HLOCATE_NEXT_COPY := HLOCATE_NEXT).
        apply incrpc'_incrpc in HLOCATE_NEXT.
        rewrite HLOCATE_NEXT in HLOCATE2.
        rewrite HLOCATE2 in HNEXT.
        des_ifs.
        { (* i2 is ptrtoint <const(int)>. *)
          exists (nil, Ir.SmallStep.sr_goes_wrong).
          split.
          - eapply Ir.SmallStep.ns_goes_wrong.
            eapply Ir.SmallStep.ns_one.
            constructor. 
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            unfold Ir.Config.get_val in *. inv Heq1. rewrite H0.
            reflexivity.
          - apply nseq_goes_wrong. reflexivity.
        }
        { (* i2 is ptrtoint <const(ptr)>. *)
          rewrite m_update_reg_and_incrpc.
          (* Needs to know that r1 != r2! from SSA property. *)
          eexists.
          split.
          - eapply Ir.SmallStep.ns_success.
            eapply Ir.SmallStep.ns_one.
            econstructor.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'. unfold Ir.Config.get_val in *. inv Heq1. rewrite H0.
            reflexivity.
            econstructor.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite HLOCATE2'.
            destruct opptr1. (* when i1's operand is constant *)
            + unfold Ir.Config.get_val in *. inv Heq0. rewrite H0.
              reflexivity.
            + rewrite get_val_independent. rewrite Heq0. reflexivity.
              admit. (* SSA property!! *)
          - rewrite m_update_reg_and_incrpc.
            apply nseq_success. reflexivity.
            eapply config_eq_wopc_update_reg_and_incrpc.
            + admit. (* SSA property. *)
        }
        { (* i2 is ptrtoint <const(poison)>. *)
          unfold Ir.Config.get_val in Heq1.
          des_ifs.
          eexists.
          split.
          - eapply Ir.SmallStep.ns_success.
            eapply Ir.SmallStep.ns_one.
            econstructor.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'. unfold Ir.Config.get_val. reflexivity.
            econstructor. unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'. rewrite HLOCATE2'.
            destruct opptr1.
            + unfold Ir.Config.get_val in *. inv Heq0. rewrite H1. reflexivity.
            + rewrite get_val_independent. rewrite Heq0. reflexivity.
              admit. (* SSA *)
          - rewrite m_update_reg_and_incrpc.
            apply nseq_success. reflexivity.
            eapply config_eq_wopc_update_reg_and_incrpc.
            admit. (* SSA *)
        }
        { exists (nil, Ir.SmallStep.sr_goes_wrong).
          split.
          - eapply Ir.SmallStep.ns_goes_wrong.
            eapply Ir.SmallStep.ns_one.
            constructor. 
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            reflexivity.
          - apply nseq_goes_wrong. reflexivity.
        }
      * simpl in HNODEP. rewrite orb_false_r in HNODEP.

Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).


End Reordering.

End Ir.
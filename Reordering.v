Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.
Require Import Omega.

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

(* Checks whether a program `i1;i2` is well-formed.
   This checks two things:
   (1) defs of i1 and i2 aren't the same (by SSA)
   (2) i1's use never contains i2's def, because i1 is never phi-node by definition of Ir.Inst.
       (Note that this is possible if i1;i2 is in a dead loop,
       but for simplity I'll assume that there's no dead loop.)
   (3) i2's use never contains i2's def, in the same reason, and
   (4) i1's use never contains i1's def. *)
Definition program_wellformed (i1 i2:Ir.Inst.t): bool :=
  match (Ir.Inst.def i2) with
  | None => true
  | Some (r2, _) =>
    match Ir.Inst.def i1 with
    | None => true
    | Some (r1, _) =>
      (negb (Nat.eqb r1 r2))
      && (negb (List.existsb (fun r => Nat.eqb r r1) (Ir.Inst.regops i1)))
    end
      && (negb (List.existsb (fun r => Nat.eqb r r2) (Ir.Inst.regops i1)))
      && (negb (List.existsb (fun r => Nat.eqb r r2) (Ir.Inst.regops i2)))
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
  rewrite Ir.Config.cur_fdef_pc_update_m.
  des_ifs. rewrite Ir.Config.update_pc_update_m. reflexivity.
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
  rewrite Ir.Config.update_rval_update_m.
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

Lemma stack_eq_wopc_incrpc:
  forall st1 st2  md1 md2
         (HEQ:Ir.Stack.eq_wopc (Ir.Config.s st1) (Ir.Config.s st2)),
    Ir.Stack.eq_wopc (Ir.Config.s (Ir.SmallStep.incrpc md1 st1))
                  (Ir.Config.s (Ir.SmallStep.incrpc md2 st2)).
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  des_ifs.
  - apply Ir.Config.stack_eq_wopc_update_pc1.
    apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc1. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc1. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
  - apply Ir.Config.stack_eq_wopc_update_pc2. assumption.
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

Lemma cur_inst_incrpc_update_m:
  forall md m st,
    Ir.Config.cur_inst md (Ir.SmallStep.incrpc md (Ir.Config.update_m st m)) =
    Ir.Config.cur_inst md (Ir.SmallStep.incrpc md st).
Proof.
  intros.
  rewrite incrpc_update_m.
  rewrite Ir.Config.cur_inst_update_m.
  reflexivity.
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
      try(rewrite incrpc_update_m; rewrite Ir.Config.cur_inst_update_m; reflexivity).
  - rewrite cur_inst_update_reg_and_incrpc.
    rewrite incrpc_update_m.
    rewrite Ir.Config.cur_inst_update_m.
    reflexivity.
Qed.

Lemma m_incrpc_update_m:
  forall md' st t,
    Ir.Config.m (Ir.SmallStep.incrpc md' (Ir.Config.update_m st t)) = t.
Proof.
  intros.
  rewrite incrpc_update_m.
  reflexivity.
Qed.

Lemma get_val_incrpc_update_m:
  forall md' st op11 t,
    Ir.Config.get_val (Ir.SmallStep.incrpc md' (Ir.Config.update_m st t)) op11 =
    Ir.Config.get_val st op11.
Proof.
  intros.
  rewrite incrpc_update_m.
  rewrite Ir.Config.get_val_update_m.
  rewrite get_val_incrpc.
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
    (HNODEP:has_data_dependency i1 i2 = false)
    (HPROGWF:program_wellformed i1 i2 = true),
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

(* Lemma: Ir.SmallStep.p2N returns unchanged value even
   if Memory.new is called *)
Lemma p2N_new_invariant:
  forall md st op l0 o0 m' l blkty nsz a c P n0
         (HWF:Ir.Config.wf md st)
         (HGV: Ir.Config.get_val st op = Some (Ir.ptr (Ir.plog l0 o0)))
         (HNEW:(m', l) = Ir.Memory.new (Ir.Config.m st) blkty nsz a c P)
         (HDISJ:Ir.Memory.allocatable (Ir.Config.m st)
                (List.map (fun addr => (addr, nsz)) P) = true)
         (HSZ2:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) c P)),
    Ir.SmallStep.p2N (Ir.plog l0 o0) (Ir.Config.m (Ir.Config.update_m st m')) n0 =
    Ir.SmallStep.p2N (Ir.plog l0 o0) (Ir.Config.m st) n0.
Proof.
  intros.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  destruct HWF.
  dup HGV.
  apply wf_no_bogus_ptr in HGV0.
  assert (HL:l = Ir.Memory.fresh_bid (Ir.Config.m st)).
  { unfold Ir.Memory.new in HNEW. inv HNEW. reflexivity. }
  erewrite Ir.Memory.get_new; try eassumption. reflexivity.
Qed. 

Ltac get_val_independent_goal opval r2 :=
  rewrite get_val_independent2;
  try (destruct opval as [| r00];
       try congruence).

Ltac get_val_independent_H H opval r2 :=
  rewrite get_val_independent2 in H;
  try (destruct opval as [| r00];
       try congruence);
  try rewrite Ir.Config.get_val_update_m in H.


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
        eapply Ir.SmallStep.s_malloc_null. rewrite cur_inst_update_reg_and_incrpc.
        apply incrpc'_incrpc in HLOCATE_NEXT'. rewrite HLOCATE_NEXT' in HLOCATE2'. rewrite HLOCATE2'. reflexivity.
        reflexivity.
      * rewrite nstep_eq_trans_1. apply nseq_success. reflexivity.
        get_val_independent_goal opptr2 r1.
        rewrite m_update_reg_and_incrpc.
        apply Ir.Config.eq_wopc_refl.
        rewrite m_update_reg_and_incrpc.
        apply Ir.Config.eq_wopc_refl.
        { (* r00 <> r1 *)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          assert (r00 <> r1). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            destruct (r00 =? r1).
            { simpl in HPROGWF. inv HNODEP. }
            { reflexivity. }
          } congruence.
        }
        { (* r1 <> r2 *)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r1 =? r2).
          { inv HPROGWF. }
           reflexivity.
        }
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
        { (* r <> r2*)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r2). { simpl in HPROGWF. repeat (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
                              { reflexivity. }
        }
        assumption.
        reflexivity. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
      * eapply nstep_eq_trans_2 with (md1 := md').
        { (* r2 <> r1 *)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          assert (r1 <> r2). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            destruct (r1 =? r2).
            { simpl in HPROGWF. inv HPROGWF. }
            { reflexivity. }
          } congruence.
        }
        rewrite update_reg_and_incrpc_update_m with (m := m') (md := md).
        rewrite Ir.Config.get_val_update_m.
        (* now we should show that opptr2 isn't something like (l, ofs).
           Note that l is a new block id. *)
        (* opptr2 (which is operand of ptrtoint) cannot be log (l, 0). *)
        destruct opptr2.
        -- rewrite get_val_const_update_reg_and_incrpc.
           destruct (Ir.Config.get_val st (Ir.opconst c)) eqn:Hopc.
           { destruct v; try do_nseq_refl.
             - destruct p.
               + destruct ty2.
                 *  (* about logical pointer *)
                   erewrite p2N_new_invariant; try eassumption. apply nstep_eq_refl.
                 * apply nstep_eq_refl.
               + unfold Ir.SmallStep.p2N. do_nseq_refl.
           }
           { do_nseq_refl. }
        -- rewrite get_val_independent.
           destruct (Ir.Config.get_val st (Ir.opreg r)) eqn:Hopr.
           { destruct v; try do_nseq_refl.
             - destruct p.
               + destruct ty2.
                 * erewrite p2N_new_invariant; try eassumption. apply nstep_eq_refl.
                 * apply nstep_eq_refl.
               + unfold Ir.SmallStep.p2N. do_nseq_refl.
           }
           { do_nseq_refl. }
           { (* r <> r1 *)
             unfold has_data_dependency in HNODEP. simpl in HNODEP.
             assert (r <> r1). {
               rewrite <- PeanoNat.Nat.eqb_neq.
               destruct (r =? r1).
               { simpl in HNODEP. inv HNODEP. }
               { reflexivity. }
             } congruence.
           }
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
      get_val_independent_goal opptr1 r2.
      eassumption. eassumption.
      {
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        assert (r00 <> r2). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r00 =? r2).
          { simpl in HPROGWF. rewrite andb_false_r in HPROGWF.
            inv HPROGWF. }
          { reflexivity. }
        } congruence.
      }
      rewrite m_update_reg_and_incrpc. assumption.
      constructor. reflexivity.
    + inv HSUCC.
    + inv HOOM0.
  - (* malloc raised goes_wrong - impossible *)
    inv HGW.
    + inv HSINGLE.
      unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence.
    + inv HSUCC.
    + inv HGW0.
Qed.



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
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      eexists. split.
      {
        eapply Ir.SmallStep.ns_success.
        {
          eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_malloc_null.
          rewrite HLOCATE1'. reflexivity. reflexivity.
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
        get_val_independent_goal opptr1 r2.
        apply nstep_eq_refl. apply nstep_eq_refl.
        {
          assert (r00 <> r2). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            unfold program_wellformed in HPROGWF. simpl in HPROGWF.
            destruct (r00 =? r2).
            { simpl in HPROGWF. rewrite andb_false_r in HPROGWF. inv HPROGWF. }
            { reflexivity. }
          }
          congruence.
        }
        { (* r1 <> r2*)
          rewrite <- PeanoNat.Nat.eqb_neq.
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          destruct (r1 =? r2).
          { simpl in HPROGWF. inv HPROGWF. }
          { reflexivity. }
        }
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
        get_val_independent_H HSZ opptr2 r1.
        eassumption.
        rewrite m_update_reg_and_incrpc in HNOSPACE. assumption.
        { (* r00 <> r1 *)
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          assert (r00 <> r1). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            destruct (r00 =? r1).
            { simpl in HNODEP. inv HNODEP. }
            { reflexivity. }
          } congruence.
        }
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
        get_val_independent_H HSZ opptr2 r1. eassumption. eassumption.
        { (* r00 <> r1 *)
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          assert (r00 <> r1). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            destruct (r00 =? r1).
            { simpl in HNODEP. inv HNODEP. }
            { reflexivity. }
          } congruence.
        }
        eassumption.
        reflexivity. eassumption. eassumption.
        eassumption.
        eapply Ir.SmallStep.s_det.
        unfold Ir.SmallStep.inst_det_step.
        rewrite cur_inst_update_reg_and_incrpc.
        rewrite incrpc_update_m.
        rewrite Ir.Config.cur_inst_update_m.
        apply incrpc'_incrpc in HLOCATE_NEXT'.
        rewrite HLOCATE_NEXT' in HLOCATE2'.
        rewrite HLOCATE2'. reflexivity.
      }
      { eapply nstep_eq_trans_2 with (md2 := md').
        { (* r1 <> r2 *)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          assert (r1 <> r2). {
            rewrite <- PeanoNat.Nat.eqb_neq.
            destruct (r1 =? r2).
            { simpl in HPROGWF. inv HPROGWF. }
            { reflexivity. }
          } congruence.
        }
        get_val_independent_goal opptr1 r2.

        rewrite Ir.Config.get_val_update_m.
        rewrite m_update_reg_and_incrpc.
        destruct (Ir.Config.get_val st (Ir.opconst c)) eqn:Hopptr1; try apply nstep_eq_refl.
        destruct v; try apply nstep_eq_refl.
        destruct p; destruct ty1; try apply nstep_eq_refl.
        erewrite p2N_new_invariant; try eassumption. apply nstep_eq_refl.

        rewrite Ir.Config.get_val_update_m.
        rewrite m_update_reg_and_incrpc.
        destruct (Ir.Config.get_val st (Ir.opreg r00)) eqn:Hopptr1; try apply nstep_eq_refl.
        destruct v; try apply nstep_eq_refl.
        destruct p; destruct ty1; try apply nstep_eq_refl.
        erewrite p2N_new_invariant; try eassumption. apply nstep_eq_refl.

        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        assert (r00 <> r2). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r00 =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        } congruence.
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
Qed.



(********************************************
   REORDERING of free - ptrtoint:

   free opptr1
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2
   free opptr1
**********************************************)

(* Lemma: Ir.SmallStep.p2N returns unchanged value even
   if Memory.free is called *)
Lemma p2N_free_invariant:
  forall md st op l0 o0 m' l n0
         (HWF:Ir.Config.wf md st)
         (HGV: Ir.Config.get_val st op = Some (Ir.ptr (Ir.plog l0 o0)))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.p2N (Ir.plog l0 o0) m' n0 =
    Ir.SmallStep.p2N (Ir.plog l0 o0) (Ir.Config.m st) n0.
Proof.
  intros.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  destruct (Ir.Memory.get m' l0) eqn:Hget';
  destruct (Ir.Memory.get (Ir.Config.m st) l0) eqn:Hget; try reflexivity.
  { rewrite Ir.Memory.get_free with (m := Ir.Config.m st) (m' := m')
                          (l := l) (l0 := l0) (blk := t0) (blk' := t).
    reflexivity.
    { destruct HWF. assumption. }
    { assumption. }
    { congruence. }
    { congruence. }
  }
  { assert (Ir.Memory.get m' l0 = None).
    { eapply Ir.Memory.get_free_none.
      { destruct HWF. eassumption. }
      { eassumption. }
      { eassumption. }
    }
    congruence.
  }
  { assert (exists blk', Ir.Memory.get m' l0 = Some blk').
    { eapply Ir.Memory.get_free_some.
      { destruct HWF. eassumption. }
      { eassumption. }
      { eassumption. }
    }
    destruct H.
    congruence.
  }
Qed.

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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    rewrite incrpc_update_m in HNEXT.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite Ir.Config.cur_inst_update_m in HNEXT.
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
      get_val_independent_goal opptr1 r2.
      rewrite m_update_reg_and_incrpc, Heq, Heq0.
      reflexivity.
      rewrite m_update_reg_and_incrpc, Heq, Heq0.
      reflexivity.

      unfold program_wellformed in HPROGWF. simpl in HPROGWF.
      assert (r00 <> r2). {
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r00 =? r2).
        { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
        { reflexivity. }
      } congruence.
    }
    { rewrite Ir.Config.get_val_update_m.
      rewrite get_val_incrpc.
      rewrite nstep_eq_trans_3 with (md2 := md').
      destruct retty2.
      - destruct (Ir.Config.get_val st opptr2) eqn:Hopptr2.
        + destruct v;try apply nstep_eq_refl.
          unfold Ir.SmallStep.free in Heq0.
          destruct p0.
          { des_ifs.
            { erewrite p2N_free_invariant. apply nstep_eq_refl.
              eassumption. eassumption. symmetry in Heq0. eassumption. }
            { erewrite p2N_free_invariant. apply nstep_eq_refl.
              eassumption. eassumption. symmetry in Heq0. eassumption. }
          }
          { unfold Ir.SmallStep.p2N. apply nstep_eq_refl. }
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

        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        assert (r <> r2). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        } congruence.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HGW0.
Qed.



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
          rewrite Ir.Config.cur_inst_update_m; rewrite HLOCATE2';
          reflexivity
        ]
      |
        rewrite Ir.Config.get_val_update_m; rewrite get_val_incrpc; rewrite Heq1;
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
          rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
          reflexivity. }
      }
      { rewrite Ir.Config.get_val_update_m. rewrite get_val_incrpc. rewrite Heq1.
        rewrite <- nstep_eq_trans_3 with (md1 := md').
        rewrite m_update_m.
        unfold Ir.SmallStep.free in Heq0.
        destruct p0.
        { des_ifs.
          { erewrite <- p2N_free_invariant. apply nstep_eq_refl.
            eassumption. eassumption. symmetry in Heq0. eassumption. }
          { erewrite <- p2N_free_invariant. apply nstep_eq_refl.
            eassumption. eassumption. symmetry in Heq0. eassumption. }
        }
        { unfold Ir.SmallStep.p2N. apply nstep_eq_refl. }
      }
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
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
      { (* r <> r1 *)
        unfold has_data_dependency in HNODEP. simpl in HNODEP.
        assert (r <> r1). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. inv HNODEP. }
          { reflexivity. }
        } congruence.
      }
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
Qed.



(********************************************
   REORDERING of ptrtoint - inttoptr:

   r1 = ptrtoint opptr1 ty1
   r2 = inttoptr opint2 ty2
   ->
   r2 = inttoptr opint2 ty2
   r1 = ptrtoint opptr1 ty1
**********************************************)

Theorem reorder_ptrtoint_inttoptr:
  forall i1 i2 r1 r2 (opptr1 opint2:Ir.op) retty1 retty2
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 retty1)
         (HINST2:i2 = Ir.Inst.iinttoptr r2 opint2 retty2),
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
    rewrite get_val_independent2 in HNEXT.
    inv HNEXT.
    eexists. split.
    { eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite cur_inst_update_reg_and_incrpc.
      rewrite HLOCATE2'. reflexivity.
    }
    { rewrite m_update_reg_and_incrpc.
      rewrite nstep_eq_trans_1 with (md2 := md').
      rewrite get_val_independent2.
      apply nstep_eq_refl.
      destruct opptr1. congruence.
      unfold program_wellformed in HPROGWF. simpl in HPROGWF.
      assert (r <> r2). {
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r =? r2).
        { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
        { reflexivity. }
      } congruence.
      unfold program_wellformed in HPROGWF. simpl in HPROGWF.
      assert (r1 <> r2). {
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r1 =? r2).
        { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
        { reflexivity. }
      } congruence.
    }
    { destruct opint2. congruence.
      { (* r <> r1 *)
        unfold has_data_dependency in HNODEP. simpl in HNODEP.
        assert (r <> r1). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. inv HNODEP. }
          { reflexivity. }
        } congruence.
      }
    }
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
Qed.



(********************************************
   REORDERING of inttoptr - ptrtoint:

   r1 = inttoptr opint1 ty1
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2
   r1 = inttoptr opint1 ty1
**********************************************)

Theorem reorder_inttoptr_ptrtoint:
  forall i1 i2 r1 r2 (opint1 opptr2:Ir.op) retty1 retty2
         (HINST1:i1 = Ir.Inst.iinttoptr r1 opint1 retty1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 retty2),
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
    rewrite get_val_independent2 in HNEXT.
    inv HNEXT.
    eexists. split.
    { eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite cur_inst_update_reg_and_incrpc.
      rewrite HLOCATE2'. reflexivity.
    }
    { rewrite m_update_reg_and_incrpc.
      rewrite nstep_eq_trans_1 with (md2 := md').
      rewrite get_val_independent2.
      apply nstep_eq_refl.
      destruct opint1. congruence.
      {
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        assert (r <> r2). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        } congruence.
      }
      {
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        assert (r1 <> r2). {
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r1 =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        } congruence.
      }
    }
    destruct opptr2. congruence.
    { (* r <> r1 *)
      unfold has_data_dependency in HNODEP. simpl in HNODEP.
      assert (r <> r1). {
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r =? r1).
        { simpl in HNODEP. inv HNODEP. }
        { reflexivity. }
      } congruence.
    }
  - (* ptrtoint never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* ptrtoint never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Qed.



(********************************************
   REORDERING of malloc - getelementptr:

   r1 = malloc ty opptr1
   r2 = gep rety opptr2 ty2
   ->
   r2 = gep rety opptr2 ty2
   r1 = malloc ty opptr1.
**********************************************)

Lemma gep_new_invariant:
  forall md l m' l0 o0 n ty2 st nsz inb contents P op
         (HWF:Ir.Config.wf md st)
         (HGV: Ir.Config.get_val st op = Some (Ir.ptr (Ir.plog l0 o0)))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.gep (Ir.plog l0 o0) n ty2 (Ir.Config.m (Ir.Config.update_m st m')) inb =
    Ir.SmallStep.gep (Ir.plog l0 o0) n ty2 (Ir.Config.m st) inb.
Proof.
  intros.
  unfold Ir.SmallStep.gep.
  erewrite Ir.Memory.get_new with (m := Ir.Config.m st).
  { reflexivity. }
  { destruct HWF. eassumption. }
  { rewrite m_update_m. eassumption. }
  { eassumption. }
  { eassumption. }
  { eassumption. }
  { destruct HWF. apply wf_no_bogus_ptr in HGV. assumption. }
Qed.

Theorem reorder_malloc_gep:
  forall i1 i2 r1 r2 opptr1 opptr2 opidx2 ty1 ty2 inb
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.igep r2 ty2 opptr2 opidx2 inb),
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
    unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence.
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
        eapply Ir.SmallStep.s_malloc_null. rewrite cur_inst_update_reg_and_incrpc.
        rewrite HLOCATE2'. reflexivity. reflexivity.
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR; congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in HNEXT.
        rewrite HLOCATE2 in HNEXT.
        inv HNEXT.
        rewrite get_val_independent2. rewrite m_update_reg_and_incrpc.
        rewrite get_val_independent2.
        rewrite nstep_eq_trans_1 with (md2 := md'). apply nseq_success. reflexivity.
        apply Ir.Config.eq_wopc_refl.
        assert (r1 <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r1 =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        }
        assumption.
        destruct opidx2. congruence.
        assert (r <> r1).
        {
          rewrite <- PeanoNat.Nat.eqb_neq.
          unfold has_data_dependency in HNODEP. destruct opptr2; simpl in HNODEP;
          destruct (r =? r1); try reflexivity.
          { simpl in HNODEP. inv HNODEP. }
          { simpl in HNODEP. rewrite orb_true_r in HNODEP. inv HNODEP. }
        }
        congruence.
        destruct opptr2. congruence.
        assert (r <> r1).
        {
          rewrite <- PeanoNat.Nat.eqb_neq.
          unfold has_data_dependency in HNODEP. destruct opidx2; simpl in HNODEP;
          destruct (r =? r1); try reflexivity.
          { simpl in HNODEP. inv HNODEP. }
          { simpl in HNODEP. inv HNODEP. }
        }
        congruence.
    + (* malloc succeeded. *)
      rewrite HLOCATE1 in HCUR. inv HCUR.
      eexists.
      split.
      * eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite HLOCATE1'.  reflexivity.
        (* and, run malloc. *)
        eapply Ir.SmallStep.s_malloc. rewrite cur_inst_update_reg_and_incrpc.
        rewrite HLOCATE2'. reflexivity.
        reflexivity.
        rewrite get_val_independent2. eassumption.
        destruct opptr1. congruence.
        assert (r <> r2).
        { unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r2).
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        }
        congruence.
        assumption. reflexivity. eassumption. rewrite m_update_reg_and_incrpc. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                          rewrite incrpc_update_m in HCUR;
                          rewrite Ir.Config.cur_inst_update_m in HCUR; congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in HNEXT.
        rewrite incrpc_update_m in HNEXT. rewrite Ir.Config.cur_inst_update_m in HNEXT.
        rewrite HLOCATE2 in HNEXT.
        inv HNEXT.
        rewrite m_update_reg_and_incrpc. Print Ltac get_val_independent_goal.
        rewrite get_val_independent2.
        rewrite get_val_independent2.
        rewrite Ir.Config.get_val_update_m. rewrite Ir.Config.get_val_update_m.
        eapply nstep_eq_trans_2 with (md1 := md').
        assert (r2 <> r1).
        { unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r1 =? r2) eqn:HR1R2.
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { rewrite Nat.eqb_sym. assumption. }
        } congruence.
        destruct ty2; try (apply nstep_eq_refl; fail).
        destruct (Ir.Config.get_val st opptr2) eqn:Hopptr2; try (apply nstep_eq_refl; fail).
        destruct v; try (apply nstep_eq_refl; fail).
        destruct (Ir.Config.get_val st opidx2) eqn:Hopidx2; try (apply nstep_eq_refl; fail).
        destruct v; try (apply nstep_eq_refl; fail).
        destruct p.
        { assert (HGEP:
                  Ir.SmallStep.gep (Ir.plog b n0) n ty2 (Ir.Config.m (Ir.Config.update_m st m')) inb =
                  Ir.SmallStep.gep (Ir.plog b n0) n ty2 (Ir.Config.m st) inb).
          { eapply gep_new_invariant; eassumption. }
          rewrite HGEP. apply nstep_eq_refl. }
        { unfold Ir.SmallStep.gep. apply nstep_eq_refl. }
        destruct opidx2. congruence.
        assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HNODEP;
          destruct (r =? r1);
          try (try (rewrite orb_true_r in HNODEP); inv HNODEP; fail);
          reflexivity.
        } congruence.
        destruct opptr2. congruence.
        assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opidx2; simpl in HNODEP;
          destruct (r =? r1);
          try (try (rewrite orb_true_r in HNODEP); inv HNODEP; fail);
          reflexivity.
        } congruence.
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
      rewrite HLOCATE2'. reflexivity. reflexivity.
      rewrite HLOCATE1 in HCUR. inv HCUR.
      destruct opptr1.
      * rewrite get_val_const_update_reg_and_incrpc. eassumption.
      * rewrite get_val_independent. assumption.
        { (* r <> r2*)
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r2) eqn:HE.
          { simpl in HPROGWF. try (rewrite andb_false_r in HPROGWF). inv HPROGWF. }
          { reflexivity. }
        }
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
Qed.



(********************************************
   REORDERING of gep - malloc:

   r1 = gep rety opptr1 opidx1 inb
   r2 = malloc ty opptr2
   ->
   r2 = malloc ty opptr2
   r1 = gep rety opptr1 opidx1 inb
**********************************************)

Theorem reorder_gep_malloc:
  forall i1 i2 r1 r2 (opptr1 opidx1 opptr2:Ir.op) (inb:bool) ty1 ty2
         (HINST1:i1 = Ir.Inst.igep r1 ty1 opptr1 opidx1 inb)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* gep succeed - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      eexists. split.
      {
        eapply Ir.SmallStep.ns_success.
        {
          eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_malloc_null.
          rewrite HLOCATE1'. reflexivity. reflexivity.
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
        rewrite get_val_independent2.
        apply nstep_eq_refl.
        destruct opidx1. congruence.
        assert (r <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr1; destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2);
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
        destruct opptr1. congruence.
        assert (r <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2);
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
        assert (r1 <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r1 =? r2);
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
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
        assert (r <> r1).
        {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }
        } congruence.
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
        assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }
        } congruence.
        assumption. reflexivity. eassumption. eassumption.
        eassumption.
        eapply Ir.SmallStep.s_det.
        unfold Ir.SmallStep.inst_det_step.
        rewrite cur_inst_update_reg_and_incrpc.
        rewrite incrpc_update_m.
        rewrite Ir.Config.cur_inst_update_m.
        apply incrpc'_incrpc in HLOCATE_NEXT'.
        rewrite HLOCATE_NEXT' in HLOCATE2'.
        rewrite HLOCATE2'. reflexivity.
      }
      { eapply nstep_eq_trans_2 with (md2 := md').
        assert (r1 <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r1 =? r2);
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } assumption.
        rewrite get_val_independent2.
        rewrite get_val_independent2.
        rewrite Ir.Config.get_val_update_m.
        rewrite m_update_reg_and_incrpc.
        destruct (Ir.Config.get_val st opptr1) eqn:Hopptr1; try apply nstep_eq_refl.
        destruct v; try apply nstep_eq_refl.
        destruct ty1; try apply nstep_eq_refl.
        rewrite Ir.Config.get_val_update_m.
        destruct (Ir.Config.get_val st opidx1) eqn:Hopidx1; try apply nstep_eq_refl.
        destruct v; try apply nstep_eq_refl.
        destruct p; try (unfold Ir.SmallStep.gep; apply nstep_eq_refl).
        assert (HGEP:
                  Ir.SmallStep.gep (Ir.plog b n0) n ty1 (Ir.Config.m (Ir.Config.update_m st m')) inb =
                  Ir.SmallStep.gep (Ir.plog b n0) n ty1 (Ir.Config.m st) inb).
        { eapply gep_new_invariant; eassumption. }
        rewrite HGEP. apply nstep_eq_refl.
        destruct opidx1. congruence.
        assert (r <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr1; destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF; fail);
          try reflexivity.
        } congruence.
        destruct opptr1. congruence.
        assert (r <> r2).
        {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF; fail);
          try reflexivity.
        } congruence.
      }
  - (* gep never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.igep r1 ty1 opptr1 opidx1 inb)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* gep never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.igep r1 ty1 opptr1 opidx1 inb)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Qed.



(********************************************
   REORDERING of free - gep:

   free opptr1
   r2 = gep retty2 opptr2 opidx2 inb
   ->
   r2 = gep retty2 opptr2 opidx2 inb
   free opptr1
**********************************************)

Lemma get_free_inbounds:
  forall m m' l l0 blk blk' o
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l)
         (HGET: Some blk  = Ir.Memory.get m l0)
         (HGET':Some blk' = Ir.Memory.get m' l0),
    Ir.MemBlock.inbounds o blk = Ir.MemBlock.inbounds o blk'.
Proof.
  intros.
  assert (Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (PeanoNat.Nat.eqb l l0) eqn:HLEQ.
  { rewrite PeanoNat.Nat.eqb_eq in HLEQ.
    subst l.
    Check Ir.Memory.get_set_id.
    rewrite Ir.Memory.get_set_id with (m := Ir.Memory.incr_time m)
      (mb := blk)
      (mb' := t0) (m' := Ir.Memory.set (Ir.Memory.incr_time m) l0 t0) in HGET';
      try congruence.
    { unfold Ir.MemBlock.set_lifetime_end in Heq2.
      destruct (Ir.MemBlock.alive t).
      { inv Heq2. inv HGET'. rewrite Heq in HGET.
        inv HGET. unfold Ir.MemBlock.inbounds.
        simpl. reflexivity. }
      { congruence. }
    }
    { apply Ir.Memory.incr_time_wf with (m := m). assumption.
      reflexivity. }
    { unfold Ir.Memory.get in *.
      unfold Ir.Memory.incr_time. simpl. congruence.
    }
  }
  { rewrite PeanoNat.Nat.eqb_neq in HLEQ.
    rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time m)
                              (mb' := t0) (mb := blk) (bid' := l)
      in HGET'; try assumption; try congruence.
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { rewrite Ir.Memory.get_incr_time_id. congruence. }
  }
Qed.

(* Lemma: Ir.SmallStep.gep returns unchanged value even
   if Memory.free is called *)
Lemma gep_free_invariant:
  forall md st op p m' l n inb ty
         (HWF:Ir.Config.wf md st)
         (HGV: Ir.Config.get_val st op = Some (Ir.ptr p))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.gep p n ty m' inb =
    Ir.SmallStep.gep p n ty (Ir.Config.m st) inb.
Proof.
  intros.
  destruct p as [l0 o0 | ].
  { 
    unfold Ir.SmallStep.gep.
    destruct (Ir.Memory.get m' l0) eqn:Hget';
      destruct (Ir.Memory.get (Ir.Config.m st) l0) eqn:Hget; try reflexivity.
    { repeat (rewrite get_free_inbounds with (m := Ir.Config.m st) (m' := m')
                                             (l := l) (l0 := l0) (blk := t0) (blk' := t));
        try ( destruct HWF; assumption );
        try congruence;
        try eassumption.
    }
    { assert (Ir.Memory.get m' l0 = None).
      { eapply Ir.Memory.get_free_none.
        { destruct HWF. eassumption. }
        { eassumption. }
        { eassumption. }
      }
      congruence.
    }
    { assert (exists blk', Ir.Memory.get m' l0 = Some blk').
      { eapply Ir.Memory.get_free_some.
        { destruct HWF. eassumption. }
        { eassumption. }
        { eassumption. }
      }
      destruct H.
      congruence.
    }
  }
  { unfold Ir.SmallStep.gep.
    simpl. reflexivity. }
Qed.

Theorem reorder_free_gep:
  forall i1 i2 r2 opptr1 (opptr2 opidx2:Ir.op) retty2 (inb:bool)
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.igep r2 retty2 opptr2 opidx2 inb),
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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    rewrite incrpc_update_m in HNEXT.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite Ir.Config.cur_inst_update_m in HNEXT.
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
      destruct opptr1. congruence.
      assert (r <> r2). {
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct opidx2; destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
      } congruence.
    }
    { rewrite Ir.Config.get_val_update_m.
      rewrite get_val_incrpc.
      rewrite nstep_eq_trans_3 with (md2 := md').
      destruct retty2.
      - destruct (Ir.Config.get_val st opptr2) eqn:Hopptr2.
        + destruct v;try apply nstep_eq_refl.
        + apply nstep_eq_refl.
      - rewrite Ir.Config.get_val_update_m.
        rewrite get_val_incrpc.
        destruct (Ir.Config.get_val st opptr2) eqn:Hopptr2; try apply nstep_eq_refl.
        destruct (v) ; try apply nstep_eq_refl.
        destruct (Ir.Config.get_val st opidx2) eqn:Hopidx2; try apply nstep_eq_refl.
        destruct (v0) ; try apply nstep_eq_refl.
        unfold Ir.SmallStep.free in Heq0.
        des_ifs.
        { assert (HGEP:Ir.SmallStep.gep p0 n retty2 t inb =
                       (Ir.SmallStep.gep p0 n retty2
                                         (Ir.Config.m st) inb)).
          { eapply gep_free_invariant. eassumption. eassumption. eauto. }
          rewrite HGEP. apply nstep_eq_refl.
        }
        { assert (HGEP:Ir.SmallStep.gep p0 n retty2 t inb =
                       (Ir.SmallStep.gep p0 n retty2
                                         (Ir.Config.m st) inb)).
          { eapply gep_free_invariant. eassumption. eassumption. eauto. }
          rewrite HGEP. apply nstep_eq_refl.
        }
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
        assert (r <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HGW0.
Qed.



(********************************************
   REORDERING of gep - free:

   r1 = gep retty1 opptr1 opidx1 inb
   free opptr2
   ->
   free opptr2
   r1 = gep retty1 opptr1 opidx1 inb
**********************************************)

Theorem reorder_gep_free:
  forall i1 i2 r1 (opptr1 opptr2 opidx1:Ir.op) retty1 inb
         (HINST1:i1 = Ir.Inst.igep r1 retty1 opptr1 opidx1 inb)
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
          rewrite Ir.Config.cur_inst_update_m; rewrite HLOCATE2';
          reflexivity
        ]
      |
        rewrite Ir.Config.get_val_update_m; rewrite get_val_incrpc; rewrite Heq1;
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
          rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
          reflexivity. }
      }
      { rewrite <- nstep_eq_trans_3 with (md1 := md'). apply nstep_eq_refl. }
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
      reflexivity.
      rewrite <- nstep_eq_trans_3 with (md1 := md').
      repeat (rewrite update_reg_and_incrpc_update_m).
      repeat (rewrite Ir.Config.get_val_update_m).
      repeat (rewrite get_val_incrpc).
      rewrite Heq1. rewrite Heq2. rewrite m_update_m.
      unfold Ir.SmallStep.free in Heq0.
      des_ifs.
      { assert (HGEP:Ir.SmallStep.gep p0 n t0 (Ir.Config.m st) inb =
                     Ir.SmallStep.gep p0 n t0 t inb).
        { erewrite <- gep_free_invariant. reflexivity.
          eassumption. eassumption. symmetry in Heq0. eassumption. }
        rewrite HGEP. apply nstep_eq_refl. }
      { assert (HGEP:Ir.SmallStep.gep p0 n t0 (Ir.Config.m st) inb =
                     Ir.SmallStep.gep p0 n t0 t inb).
        { erewrite <- gep_free_invariant. reflexivity.
          eassumption. eassumption. symmetry in Heq0. eassumption. }
        rewrite HGEP. apply nstep_eq_refl. }
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
      reflexivity.
      rewrite <- nstep_eq_trans_3 with (md1 := md').
      repeat (rewrite update_reg_and_incrpc_update_m).
      repeat (rewrite Ir.Config.get_val_update_m).
      repeat (rewrite get_val_incrpc).
      rewrite Heq1. rewrite Heq2. apply nstep_eq_refl.
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
      reflexivity.
      rewrite <- nstep_eq_trans_3 with (md1 := md').
      repeat (rewrite update_reg_and_incrpc_update_m).
      repeat (rewrite Ir.Config.get_val_update_m).
      repeat (rewrite get_val_incrpc).
      rewrite Heq1. rewrite Heq2. apply nstep_eq_refl.
    + eexists. split. eapply Ir.SmallStep.ns_success.
      eapply Ir.SmallStep.ns_one.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
      rewrite Heq. rewrite Heq0. reflexivity.
      eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
      rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
      reflexivity.
      rewrite <- nstep_eq_trans_3 with (md1 := md').
      repeat (rewrite update_reg_and_incrpc_update_m).
      repeat (rewrite Ir.Config.get_val_update_m).
      repeat (rewrite get_val_incrpc).
      rewrite Heq1. rewrite Heq2. apply nstep_eq_refl.
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
      assert (r <> r1). {
        unfold has_data_dependency in HNODEP. simpl in HNODEP.
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r =? r1).
        { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
        { reflexivity. }
      } congruence.
  - (* ptrtoint never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.igep r1 retty1 opptr1 opidx1 inb)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* ptrtoint never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.igep r1 retty1 opptr1 opidx1 inb)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Qed.


(********************************************
   REORDERING of malloc - inttoptr:

   r1 = malloc ty opptr1
   r2 = inttoptr opint2 retty2
   ->
   r2 = inttoptr opint2 retty2
   r1 = malloc ty opptr1.
**********************************************)

Theorem reorder_malloc_inttoptr:
  forall i1 i2 r1 r2 (opptr1 opint2:Ir.op) ty1 retty2
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.iinttoptr r2 opint2 retty2),
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
    unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. congruence.
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
        eapply Ir.SmallStep.s_malloc_null. rewrite cur_inst_update_reg_and_incrpc.
        rewrite HLOCATE2'. reflexivity. reflexivity.
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR; congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in HNEXT.
        rewrite HLOCATE2 in HNEXT.
        inv HNEXT.
        rewrite get_val_independent2.
        rewrite nstep_eq_trans_1 with (md2 := md'). apply nseq_success. reflexivity.
        apply Ir.Config.eq_wopc_refl.
        assert (r1 <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr1; destruct opint2; simpl in HPROGWF;
          destruct (r1 =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
        destruct opint2. congruence.
        assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }          
        } congruence.
    + (* malloc succeeded. *)
      rewrite HLOCATE1 in HCUR. inv HCUR.
      eexists.
      split.
      * eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
        rewrite HLOCATE1'.  reflexivity.
        (* and, run malloc. *)
        eapply Ir.SmallStep.s_malloc. rewrite cur_inst_update_reg_and_incrpc.
        rewrite HLOCATE2'. reflexivity.
        reflexivity.
        rewrite get_val_independent2. eassumption.
        destruct opptr1. congruence.
        assert (r <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opint2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
        assumption. reflexivity. eassumption. rewrite m_update_reg_and_incrpc. eassumption.
        rewrite m_update_reg_and_incrpc. eassumption.
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                          rewrite incrpc_update_m in HCUR;
                          rewrite Ir.Config.cur_inst_update_m in HCUR; congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in HNEXT.
        rewrite incrpc_update_m in HNEXT. rewrite Ir.Config.cur_inst_update_m in HNEXT.
        rewrite HLOCATE2 in HNEXT.
        inv HNEXT.
        rewrite get_val_independent2.
        rewrite Ir.Config.get_val_update_m.
        eapply nstep_eq_trans_2 with (md1 := md').
        assert (r2 <> r1). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opint2; destruct opptr1; simpl in HPROGWF;
          destruct (r1 =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try (rewrite PeanoNat.Nat.eqb_sym; congruence).
        } assumption.
        destruct retty2; try (apply nstep_eq_refl; fail).
        destruct opint2. congruence. assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }
        } congruence.
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
      rewrite HLOCATE2'. reflexivity. reflexivity.
      rewrite HLOCATE1 in HCUR. inv HCUR.
      destruct opptr1.
      * rewrite get_val_const_update_reg_and_incrpc. eassumption.
      * rewrite get_val_independent. assumption.
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct opint2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
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
Qed.



(********************************************
   REORDERING of inttoptr - malloc:

   r1 = inttoptr opint1 retty1
   r2 = malloc ty opptr2
   ->
   r2 = malloc ty opptr2
   r1 = inttoptr opint1 retty1
**********************************************)

Theorem reorder_inttoptr_malloc:
  forall i1 i2 r1 r2 (opint1 opptr2:Ir.op) retty1 ty2
         (HINST1:i1 = Ir.Inst.iinttoptr r1 opint1 retty1)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* gep succeed - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HLOCATE1 in HNEXT. inv HNEXT.
      eexists. split.
      {
        eapply Ir.SmallStep.ns_success.
        {
          eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_malloc_null.
          rewrite HLOCATE1'. reflexivity. reflexivity.
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
      { unfold program_wellformed in HPROGWF.
        simpl in HPROGWF.
        rewrite get_val_independent2.
        rewrite nstep_eq_trans_1 with (md2 := md').
        apply nstep_eq_refl.
        assert (r1 <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opint1; destruct opptr2; simpl in HPROGWF;
          destruct (r1 =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
        destruct opint1. congruence.
        assert (r <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
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
        assert (r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }
        }
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
      { unfold program_wellformed in HPROGWF.
        simpl in HPROGWF.
        eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc. rewrite HLOCATE1'. reflexivity. reflexivity.
        rewrite get_val_independent2 in HSZ. eassumption.
        destruct opptr2. intros H. congruence.
        assert(r <> r1). {
          unfold has_data_dependency in HNODEP. simpl in HNODEP.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct (r =? r1).
          { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
          { reflexivity. }
        }
        intros H2. congruence.
        assumption. reflexivity. eassumption. eassumption.
        eassumption.
        eapply Ir.SmallStep.s_det.
        unfold Ir.SmallStep.inst_det_step.
        rewrite cur_inst_update_reg_and_incrpc.
        rewrite incrpc_update_m.
        rewrite Ir.Config.cur_inst_update_m.
        apply incrpc'_incrpc in HLOCATE_NEXT'.
        rewrite HLOCATE_NEXT' in HLOCATE2'.
        rewrite HLOCATE2'. reflexivity.
      }
      { eapply nstep_eq_trans_2 with (md2 := md').
        assert (r1 <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r1 =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } assumption.
        rewrite get_val_independent2.
        rewrite Ir.Config.get_val_update_m.
        destruct retty1; try apply nstep_eq_refl.
        destruct opint1. congruence.
        assert (r <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opptr2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
      }
  - (* gep never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* gep never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Qed.



(********************************************
   REORDERING of free - inttoptr:

   free opptr1
   r2 = inttoptr opint2 retty2
   ->
   r2 = inttoptr opint2 retty2
   free opptr1
**********************************************)

Theorem reorder_free_inttoptr:
  forall i1 i2 r2 (opptr1 opint2:Ir.op) retty2
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.iinttoptr r2 opint2 retty2),
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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    rewrite incrpc_update_m in HNEXT.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite Ir.Config.cur_inst_update_m in HNEXT.
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
      assert (r <> r2). {
        unfold program_wellformed in HPROGWF. simpl in HPROGWF.
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct opint2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
      } congruence.
    }
    { rewrite Ir.Config.get_val_update_m.
      rewrite get_val_incrpc.
      rewrite nstep_eq_trans_3 with (md2 := md').
      destruct retty2; try apply nstep_eq_refl.
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
        assert (r <> r2). {
          unfold program_wellformed in HPROGWF. simpl in HPROGWF.
          rewrite <- PeanoNat.Nat.eqb_neq.
          destruct opint2; simpl in HPROGWF;
          destruct (r =? r2) eqn:HRR2;
          try (simpl in HPROGWF;
               try (rewrite andb_false_r in HPROGWF);
               try (rewrite orb_true_r in HPROGWF);
               try (rewrite andb_false_r in HPROGWF); inv HPROGWF);
          try reflexivity.
        } congruence.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HGW0.
Qed.


(********************************************
   REORDERING of inttoptr - free:

   r1 = inttoptr opint1 retty1
   free opptr2
   ->
   free opptr2
   r1 = inttoptr opint1 retty1
**********************************************)

Theorem reorder_inttoptr_free:
  forall i1 i2 r1 (opint1 opptr2:Ir.op) retty1
         (HINST1:i1 = Ir.Inst.iinttoptr r1 opint1 retty1)
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
          rewrite Ir.Config.cur_inst_update_m; rewrite HLOCATE2';
          reflexivity
        ]
      |
        rewrite Ir.Config.get_val_update_m; rewrite get_val_incrpc; rewrite Heq1;
        rewrite <- nstep_eq_trans_3 with (md1 := md');
        apply nstep_eq_refl
      ]; fail);
    try(
      eexists; split;
      [ eapply Ir.SmallStep.ns_goes_wrong;
        eapply Ir.SmallStep.ns_one;
        eapply Ir.SmallStep.s_det;
        unfold Ir.SmallStep.inst_det_step; rewrite HLOCATE1';
        rewrite Heq; try rewrite Heq0; reflexivity
      | constructor; reflexivity ]).
    + eexists. split.
      { eapply Ir.SmallStep.ns_success.
        { eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite HLOCATE1'.
          rewrite Heq. rewrite Heq0. reflexivity.
        }
        { eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite incrpc_update_m. 
          rewrite Ir.Config.cur_inst_update_m. rewrite HLOCATE2'.
          reflexivity. }
      }
      { rewrite <- nstep_eq_trans_3 with (md1 := md'). apply nstep_eq_refl. }
    + destruct opptr2. congruence.
      assert (r <> r1). {
        unfold has_data_dependency in HNODEP. simpl in HNODEP.
        rewrite <- PeanoNat.Nat.eqb_neq.
        destruct (r =? r1).
        { simpl in HNODEP. try (rewrite orb_true_r in HNODEP). inv HNODEP. }
        { reflexivity. }
      } congruence.
  - (* inttoptr never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* inttoptr never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iinttoptr r1 opint1 retty1)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Qed.


(********************************************
   REORDERING of malloc - icmp_eq:

   r1 = malloc ty opptr1
   r2 = icmp_eq opty2 op21 op22
   ->
   r2 = icmp_eq opty2 op21 op22
   r1 = malloc ty opptr1.
**********************************************)


Ltac inv_cur_inst HCUR HLOCATE :=
  rewrite HLOCATE in HCUR; inv HCUR.

Ltac inv_cur_inst_next HCUR HLOCATE2 HLOCATE_NEXT :=
  apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
  try (rewrite incrpc_update_m in HCUR); try (rewrite Ir.Config.cur_inst_update_m in HCUR);
  try (rewrite HLOCATE2 in HCUR); inv HCUR.

Ltac s_malloc_null_trivial HLOCATE2' :=
  eapply Ir.SmallStep.s_malloc_null;
  try (try (rewrite cur_inst_update_reg_and_incrpc);
       rewrite HLOCATE2');
  try reflexivity.

Ltac s_malloc_trivial HLOCATE2' :=
  eapply Ir.SmallStep.s_malloc;
  try (try rewrite m_update_reg_and_incrpc; eauto);
  try (rewrite cur_inst_update_reg_and_incrpc; try rewrite HLOCATE2'; reflexivity).

Ltac inst_step_det_trivial HLOCATE' Hop1 Hop2 :=
  apply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
  rewrite HLOCATE'; rewrite Hop1; try (rewrite Hop2); reflexivity.

Ltac inst_step_icmp_det_ptr_trivial HLOCATE' Hop1 Hop2 Heqptr :=
  apply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
  rewrite HLOCATE'; rewrite Hop1; rewrite Hop2; rewrite Heqptr; reflexivity.

Lemma icmp_eq_always_succeeds:
  forall st (md:Ir.IRModule.t) r opty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r opty op1 op2)),
  exists st' v,
    (Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success Ir.e_none st') /\
    (st' = Ir.SmallStep.update_reg_and_incrpc md st r v)).
Proof.
  intros.
  destruct (Ir.Config.get_val st op1) eqn:Hop1.
  { destruct v.
    { (* op1 is number *)
      destruct (Ir.Config.get_val st op2) eqn:Hop2.
      { destruct v;
          try (eexists; eexists; split;
          [ eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
              rewrite HCUR; rewrite Hop1, Hop2; reflexivity
          | reflexivity ]).
      }
      { eexists. eexists. split.
        { eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
          rewrite HCUR; rewrite Hop1, Hop2. reflexivity. }
        { reflexivity. }
      }
    }
    { destruct (Ir.Config.get_val st op2) eqn:Hop2.
      { destruct v.
        { eexists. eexists. split.
          { eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
              rewrite HCUR; rewrite Hop1, Hop2. reflexivity. }
          { reflexivity. } }
        { destruct (Ir.SmallStep.icmp_eq_ptr_nondet_cond p p0 (Ir.Config.m st))
            eqn:HDET.
          { eexists. eexists. split.
            { eapply Ir.SmallStep.s_icmp_eq_nondet.
              rewrite HCUR. reflexivity.
              reflexivity. rewrite Hop1. reflexivity.
              rewrite Hop2. reflexivity.
              eassumption. }
            { reflexivity. }
          }
          { destruct p; destruct p0; try (
              eexists; eexists; split;
              [ eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                unfold Ir.SmallStep.icmp_eq_ptr;
                rewrite HCUR, Hop1, Hop2; reflexivity
              | reflexivity]; fail).
            { destruct (PeanoNat.Nat.eqb b b0) eqn:HEQB; try (
                eexists; eexists; split; 
                [ eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  unfold Ir.SmallStep.icmp_eq_ptr;
                  rewrite HCUR, Hop1, Hop2, HDET, HEQB; reflexivity
                | reflexivity ] ).
            }
          }
        }
        { eexists. eexists. split.
          { eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite HCUR, Hop1, Hop2; reflexivity. }
          { reflexivity. }
        }
      }
      { eexists. eexists. split.
        { eapply Ir.SmallStep.s_det;
          unfold Ir.SmallStep.inst_det_step;
          rewrite HCUR, Hop1, Hop2; reflexivity. }
        { reflexivity. }
      }
    }
    { eexists. eexists. split.
      { eapply Ir.SmallStep.s_det;
        unfold Ir.SmallStep.inst_det_step;
        rewrite HCUR, Hop1; reflexivity. }
      { reflexivity. }
    }
  }
  { eexists. eexists. split.
    { eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step.
      rewrite HCUR. rewrite Hop1. reflexivity. }
    { reflexivity. }
  }
  (* Why should I do this? *) Unshelve. constructor.
Qed.


Lemma icmp_eq_always_succeeds2:
  forall st st' (md:Ir.IRModule.t) r opty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r opty op1 op2))
         (HSTEP: Ir.SmallStep.inst_step md st st'),
  exists v, st' = Ir.SmallStep.sr_success Ir.e_none
                                (Ir.SmallStep.update_reg_and_incrpc md st r v).
Proof.
  intros.
  inv HSTEP; try congruence.
  { unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    destruct (Ir.Config.get_val st op1) eqn:Hop1.
    { destruct v.
      { (* op1 is number *)
        destruct (Ir.Config.get_val st op2) eqn:Hop2.
        { des_ifs; eexists; reflexivity. }
        { inv HNEXT; eexists; reflexivity. }
      }
      { (* op1 is ptr *)
        destruct (Ir.Config.get_val st op2) eqn:Hop2.
        { des_ifs; eexists; reflexivity. }
        { inv HNEXT; eexists; reflexivity. }
      }
      { inv HNEXT. eexists. reflexivity. }
    }
    { inv HNEXT. eexists. reflexivity. }
  }
  { rewrite HCUR in HCUR0. inv HCUR0.
    eexists. reflexivity. }
Qed.

Lemma icmp_eq_ptr_nondet_cond_new_invariant:
  forall md l m' p1 p2 st nsz contents P op1 op2
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m (Ir.Config.update_m st m')) =
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  destruct p1.
  { destruct p2.
    { erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
        try reflexivity;
        try (destruct HWF; eassumption);
        try (try rewrite m_update_m; eassumption).
      destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:HGETB.
      { 
        erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
          try reflexivity;
          try (destruct HWF; eassumption);
          try (try rewrite m_update_m; eassumption).
        destruct HWF. apply wf_no_bogus_ptr in HGV2. assumption.
      }
      { reflexivity. }
      destruct HWF. apply wf_no_bogus_ptr in HGV1. assumption.
      
    }
    { reflexivity. }
  }
  { destruct p2.
    { reflexivity. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
Qed.

Lemma icmp_eq_ptr_new_invariant:
  forall md l m' p1 p2 st nsz contents P op1 op2
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.icmp_eq_ptr p1 p2 (Ir.Config.m (Ir.Config.update_m st m')) =
    Ir.SmallStep.icmp_eq_ptr p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  destruct p1.
  { destruct p2.
    { destruct (b =? b0) eqn:Heqb. reflexivity.
      erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
        try reflexivity;
        try (destruct HWF; eassumption);
        try (try rewrite m_update_m; eassumption).
      destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:HGETB.
      { 
        erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
          try reflexivity;
          try (destruct HWF; eassumption);
          try (try rewrite m_update_m; eassumption).
        destruct HWF. apply wf_no_bogus_ptr in HGV2. assumption.
      }
      { reflexivity. }
      destruct HWF. apply wf_no_bogus_ptr in HGV1. assumption.
    }
    { erewrite p2N_new_invariant; try eassumption. reflexivity. }
  }
  { destruct p2.
    { erewrite p2N_new_invariant;try eassumption. reflexivity. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
Qed.



Theorem reorder_malloc_icmp_eq:
  forall i1 i2 r1 r2 (opptr1 op21 op22:Ir.op) ty1 opty2
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.iicmp_eq r2 opty2 op21 op22),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* malloc succeeds. *)
    inv HSUCC; try (inv HSUCC0; fail).
    exploit inst_step_incrpc. eapply HLOCATE_NEXT. eapply HSINGLE0.
    intros HCUR'.
    inv HSINGLE; try congruence.
    + (* iicmp works deterministically. *)
      unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite <- HCUR' in HNEXT.
      rewrite HLOCATE2 in HNEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      (* now get malloc's behavior *)
      inv HSINGLE0; try congruence.
      * unfold Ir.SmallStep.inst_det_step in HNEXT0. rewrite HLOCATE1 in HNEXT0.
        congruence.
      * (* Malloc returned NULL. *)
        inv_cur_inst HCUR HLOCATE1.
        rewrite get_val_independent2 in HNEXT.
        rewrite get_val_independent2 in HNEXT.
        rewrite m_update_reg_and_incrpc in HNEXT.
        destruct (Ir.Config.get_val st op21) eqn:Hop21;
          destruct (Ir.Config.get_val st op22) eqn:Hop22.
        { destruct v; destruct v0; try inv HNEXT;
          try (eexists; split;
          [ eapply Ir.SmallStep.ns_success;
            [ eapply Ir.SmallStep.ns_one;
              inst_step_det_trivial HLOCATE1' Hop21 Hop22
            | s_malloc_null_trivial HLOCATE2';
              get_val_independent_goal opptr1 r2]
          | eapply nstep_eq_trans_1;
            [ assert (r1 <> r2) by admit; assumption | apply nstep_eq_refl ] ]).
          - des_ifs. eexists. split.
            + eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
              inst_step_icmp_det_ptr_trivial HLOCATE1' Hop21 Hop22 Heq.
              s_malloc_null_trivial HLOCATE2'.
            + eapply nstep_eq_trans_1. assert (r1 <> r2) by admit.
              assumption. apply nstep_eq_refl.
        }
        { destruct v; try inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { destruct op22. congruence. assert (r <> r1) by admit. congruence. }
        { destruct op21. congruence. assert (r <> r1) by admit. congruence. }
      * (* malloc succeeded. *)
        get_val_independent_H HNEXT op21 r.
        get_val_independent_H HNEXT op22 r.
        inv_cur_inst HCUR HLOCATE1.
        repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
        des_ifs; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success;
            [ apply Ir.SmallStep.ns_one;
              try inst_step_det_trivial HLOCATE1' Heq Heq0;
              try (rewrite m_update_reg_and_incrpc in Heq1;
                   inst_step_icmp_det_ptr_trivial HLOCATE1' Heq Heq0 Heq1)
            | s_malloc_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_2; [ assert (r2 <> r1) by admit; congruence 
            | apply nstep_eq_refl ]]).
        { eexists. split.
          { eapply Ir.SmallStep.ns_success.
            - apply Ir.SmallStep.ns_one.
              rewrite m_update_reg_and_incrpc in Heq1.
              apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite HLOCATE1'. rewrite Heq. rewrite Heq0.
              rewrite m_update_m in Heq1.
              assert (HPTR:Ir.SmallStep.icmp_eq_ptr p p0 (Ir.Config.m st) =
                           Ir.SmallStep.icmp_eq_ptr p p0 m').
              { erewrite <- icmp_eq_ptr_new_invariant; try eassumption.
                rewrite m_update_m. reflexivity. }
              rewrite HPTR. rewrite Heq1. reflexivity.
            - s_malloc_trivial HLOCATE2'. get_val_independent_goal opptr1 r2.
          }
          { eapply nstep_eq_trans_2; [ assert (r2 <> r1) by admit; congruence 
            | apply nstep_eq_refl ]. }
        }
    + (* icmp works nondeterministically. *)
      (*apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.*)
      inv HSINGLE0; try congruence;
        try (unfold Ir.SmallStep.inst_det_step in HNEXT;
             rewrite HLOCATE1 in HNEXT; congruence).
      * rewrite m_update_reg_and_incrpc in *.
        inv_cur_inst HCUR0 HLOCATE1.
        rewrite <- HCUR' in HCUR.
        inv_cur_inst HCUR HLOCATE2.
        get_val_independent_H HOP1 op21 r1.
        get_val_independent_H HOP2 op22 r1.
        eexists. split.
        { eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_eq_nondet.
          rewrite HLOCATE1'. reflexivity.
          reflexivity. eapply HOP1. eapply HOP2. eassumption.
          apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          s_malloc_null_trivial HLOCATE2'.
        }
        { eapply nstep_eq_trans_1.
          { assert (r1 <> r2). admit. congruence. } 
          { apply nstep_eq_refl. }
        }
      * rewrite m_update_reg_and_incrpc in *.
        rewrite cur_inst_update_reg_and_incrpc in *.
        repeat (rewrite m_update_m in *).
        inv_cur_inst_next HCUR' HLOCATE2' HLOCATE_NEXT'.
        inv_cur_inst_next HCUR HLOCATE2 HLOCATE_NEXT.
        inv_cur_inst HCUR0 HLOCATE1.
        get_val_independent_H HOP1 op21 r1.
        get_val_independent_H HOP2 op22 r1.
        eexists. split.
        { eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_eq_nondet.
          rewrite HLOCATE1'. reflexivity.
          reflexivity. eapply HOP1. eapply HOP2.
          assert (HCMP: Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 m' =
                        Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
          { erewrite <- icmp_eq_ptr_nondet_cond_new_invariant; try eassumption.
            rewrite m_update_m.
            reflexivity.
            eauto. eauto. }
          rewrite <- HCMP. assumption.
          s_malloc_trivial HLOCATE2'.
          get_val_independent_goal opptr1 r2.
        }
        { eapply nstep_eq_trans_2.
          assert (r2 <> r1). admit. congruence.
          eapply nstep_eq_refl. }
  - (* malloc raised oom. *)
    inv HOOM.
    + inv HSINGLE. unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. inv HNEXT.
      inv_cur_inst HCUR HLOCATE1.
      (* icmp only succeeds. *)
      assert (HSUCC := icmp_eq_always_succeeds st md' r2 opty2
                                                   op21 op22 HLOCATE1').
      destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        - eapply Ir.SmallStep.ns_one.
          eapply HSUCC1.
        - eapply Ir.SmallStep.s_malloc_oom.
          rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
          reflexivity.
          reflexivity.
          rewrite HSUCC2. get_val_independent_goal opptr1 r2.
          rewrite HSUCC2. rewrite m_update_reg_and_incrpc. eassumption.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HOOM0.
  - (* malloc never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.imalloc r1 ty1 opptr1)).
      reflexivity. eapply HLOCATE1. eassumption.
      intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of icmp_eq - malloc:

   r1 = icmp_eq opty1 op11 op12
   r2 = malloc ty2 opptr2
   ->
   r2 = malloc ty2 opptr2
   r1 = icmp_eq opty1 op11 op12
**********************************************)

Theorem reorder_icmp_eq_malloc:
  forall i1 i2 r1 r2 (op11 op12 opptr2:Ir.op) opty1 ty2
         (HINST1:i1 = Ir.Inst.iicmp_eq r1 opty1 op11 op12)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* icmp - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      {
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT. inv HNEXT.
        des_ifs;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ eapply Ir.SmallStep.ns_one;
                  s_malloc_null_trivial HLOCATE1';
                  get_val_independent_H HZERO opptr2 r1
                | eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite HLOCATE2';
                  get_val_independent_goal op11 r2;
                  rewrite Heq;
                  try (get_val_independent_goal op12 r2;
                       rewrite Heq0);
                  reflexivity ]
              | rewrite nstep_eq_trans_1;
                [ apply nstep_eq_refl | assert (r1 <> r2) by admit; congruence ] ]).
        { eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_null_trivial HLOCATE1'.
            }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Heq.
              get_val_independent_goal op12 r2.
              rewrite Heq0.
              rewrite m_update_reg_and_incrpc.
              rewrite Heq1.
              reflexivity.
            }
          }
          { rewrite nstep_eq_trans_1. apply nstep_eq_refl.
            assert (r1 <> r2). admit. congruence. }
        }
      }
      { rewrite HLOCATE1 in HCUR. inv HCUR.
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            s_malloc_null_trivial HLOCATE1'.
          }
          { eapply Ir.SmallStep.s_icmp_eq_nondet.
            rewrite cur_inst_update_reg_and_incrpc.
            rewrite HLOCATE2'. reflexivity.
            reflexivity.
            get_val_independent_goal op11 r2.
            get_val_independent_goal op12 r2.
            rewrite m_update_reg_and_incrpc.
            assumption.
          }
        }
        { rewrite nstep_eq_trans_1. apply nstep_eq_refl.
          assert (r1 <> r2). admit. congruence. }
      }
    + (* oom *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply icmp_eq_always_succeeds2 with (r := r1) (opty := opty1)
          (op1 := op11) (op2 := op12) in HSINGLE0.
      destruct HSINGLE0 as [vtmp HSINGLE0]. inv HSINGLE0.
      eexists (nil, Ir.SmallStep.sr_oom).
      split.
      { eapply Ir.SmallStep.ns_oom.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc_oom.
        rewrite HLOCATE1'. reflexivity. reflexivity.
        get_val_independent_H HSZ opptr2 r1. eassumption.
        rewrite m_update_reg_and_incrpc in HNOSPACE.
        assumption.
      }
      { constructor. reflexivity. }
      assumption.
    + (* malloc succeeds *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      { (* icmp is determinsitic *)
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT.
        des_ifs;
          rewrite m_update_reg_and_incrpc in *;
          rewrite cur_inst_update_reg_and_incrpc in *;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ (* malloc *)
                  eapply Ir.SmallStep.ns_one;
                  eapply Ir.SmallStep.s_malloc; try (eauto; fail);
                  try eassumption;
                  try get_val_independent_H HSZ opptr2 r1
                | (* icmp, det *)
                  eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite cur_inst_incrpc_update_m;
                  rewrite HLOCATE2';
                  get_val_independent_goal op11 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq;
                  try (get_val_independent_goal op12 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq0);
                  reflexivity
                ]
              | eapply nstep_eq_trans_2;
                [ assert (r1 <> r2) by admit; assumption
                | apply nstep_eq_refl ]
              ]).
        { (* icmp ptr deterministic *)
          eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_trivial HLOCATE1'.
              get_val_independent_H HSZ opptr2 r1. }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Ir.Config.get_val_update_m, Heq.
              get_val_independent_goal op12 r2.
              rewrite Ir.Config.get_val_update_m, Heq0.
              rewrite m_update_reg_and_incrpc.
              rewrite m_update_m.
              assert (HPTR:Ir.SmallStep.icmp_eq_ptr p p0 m' =
                           Ir.SmallStep.icmp_eq_ptr p p0 (Ir.Config.m st)).
              { erewrite <- icmp_eq_ptr_new_invariant; try eassumption.
                rewrite m_update_m. reflexivity. }
              rewrite HPTR. rewrite Heq1. reflexivity.
            }
          }
          {
            rewrite nstep_eq_trans_2.
            { apply nstep_eq_refl. }
            { assert (r1 <> r2) by admit. congruence. }
          }
        }
      }
      { (* icmp non-det. *)
        rewrite HLOCATE1 in HCUR. inv HCUR.
        rewrite m_update_reg_and_incrpc in *.
        eexists.
        split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            s_malloc_trivial HLOCATE1'.
            get_val_independent_H HSZ opptr2 r1.
          }
          { eapply Ir.SmallStep.s_icmp_eq_nondet.
            { rewrite cur_inst_update_reg_and_incrpc.
              rewrite cur_inst_incrpc_update_m.
              eauto. }
            { reflexivity. }
            { get_val_independent_goal op11 r2. }
            { get_val_independent_goal op12 r2. }
            { rewrite m_update_reg_and_incrpc.
              rewrite m_update_m.
              assert (Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 m' =
                      Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
              { erewrite <- icmp_eq_ptr_nondet_cond_new_invariant; try eassumption.
                rewrite m_update_m. reflexivity. eauto. eauto.
              }
              congruence. }
          }
        }
        { rewrite nstep_eq_trans_2.
          apply nstep_eq_refl.
          assert (r1 <> r2). admit. congruence. }
      }
  - (* icmp never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iicmp_eq r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* icmp never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iicmp_eq r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of free - icmp_eq:

   free opptr1
   r2 = icmp_eq opty2 op21 op22
   ->
   r2 = icmp_eq opty2 op21 op22
   free opptr1
**********************************************)

Lemma get_free_n:
  forall m m' l l0 blk blk'
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l)
         (HGET: Some blk  = Ir.Memory.get m l0)
         (HGET':Some blk' = Ir.Memory.get m' l0),
    Ir.MemBlock.n blk = Ir.MemBlock.n blk'.
Proof.
  intros.
  assert (Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (PeanoNat.Nat.eqb l l0) eqn:HLEQ.
  { rewrite PeanoNat.Nat.eqb_eq in HLEQ.
    subst l.
    Check Ir.Memory.get_set_id.
    rewrite Ir.Memory.get_set_id with (m := Ir.Memory.incr_time m)
      (mb := blk)
      (mb' := t0) (m' := Ir.Memory.set (Ir.Memory.incr_time m) l0 t0) in HGET';
      try congruence.
    { unfold Ir.MemBlock.set_lifetime_end in Heq2.
      destruct (Ir.MemBlock.alive t).
      { inv Heq2. inv HGET'. rewrite Heq in HGET.
        inv HGET. unfold Ir.MemBlock.inbounds.
        simpl. reflexivity. }
      { congruence. }
    }
    { apply Ir.Memory.incr_time_wf with (m := m). assumption.
      reflexivity. }
    { unfold Ir.Memory.get in *.
      unfold Ir.Memory.incr_time. simpl. congruence.
    }
  }
  { rewrite PeanoNat.Nat.eqb_neq in HLEQ.
    rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time m)
                              (mb' := t0) (mb := blk) (bid' := l)
      in HGET'; try assumption; try congruence.
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { rewrite Ir.Memory.get_incr_time_id. congruence. }
  }
Qed.

(* Lemma: Ir.SmallStep.icmp_eq_ptr_nondet_cond returns unchanged value even
   if Memory.free is called *)
Lemma icmp_eq_ptr_nondet_cond_free_invariant:
  forall md st op1 op2 p1 p2 m' l
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 m' =
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st).
Proof.
  intros.
  destruct HWF.
  assert (Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  destruct p1.
  { destruct p2.
    { destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:Hgetb.
      { dup Hgetb. apply Ir.Memory.get_free_some with (m' := m') (l0 := l) in Hgetb0.
        destruct Hgetb0 as [blk' Hgetb'].
        rewrite Hgetb'.

        destruct (Ir.Memory.get (Ir.Config.m st) b0) eqn:Hgetb1.
        { dup Hgetb1. apply Ir.Memory.get_free_some with (m' := m') (l0 := l) in Hgetb0.
          destruct Hgetb0 as [blk0' Hgetb1'].
          rewrite Hgetb1'.
          { rewrite get_free_n with (m := Ir.Config.m st) (m' := m') (l := l) (l0 := b)
                                    (blk := t) (blk':= blk'); try assumption; try congruence.
            rewrite get_free_n with (m := Ir.Config.m st) (m' := m') (l := l) (l0 := b0)
                                    (blk := t0) (blk':= blk0'); try assumption; try congruence.
            destruct (l =? b) eqn:HLB.
            { rewrite PeanoNat.Nat.eqb_eq in HLB.
              subst l.
              unfold Ir.Memory.free in HFREE.
              rewrite Hgetb in HFREE.
              destruct (Ir.MemBlock.bt t) eqn:Hbt; try congruence.
              destruct (Ir.MemBlock.alive t) eqn:Halivet; try congruence.
              destruct (Ir.MemBlock.set_lifetime_end t (Ir.Memory.mt (Ir.Config.m st))) eqn:HLIFETIME;
                try congruence.
              rewrite Ir.Memory.get_set_id with (mb' := t1) (mb := t)
                                                (m := Ir.Memory.incr_time (Ir.Config.m st)) in Hgetb'.
              { inv Hgetb'. inv HFREE. unfold Ir.MemBlock.set_lifetime_end in HLIFETIME.
                rewrite Halivet in HLIFETIME. inv HLIFETIME. simpl.
                destruct (b =? b0) eqn:HBB0.
                { rewrite PeanoNat.Nat.eqb_eq in HBB0.
                  subst b.
                  rewrite Ir.Memory.get_set_id with (m := Ir.Memory.incr_time (Ir.Config.m st))
                    (mb := t0) (mb' := {|
                                        Ir.MemBlock.bt := Ir.MemBlock.bt t;
                                        Ir.MemBlock.r := (fst (Ir.MemBlock.r t),
                                                          Some (Ir.Memory.mt (Ir.Config.m st)));
                                        Ir.MemBlock.n := Ir.MemBlock.n t;
                                        Ir.MemBlock.a := Ir.MemBlock.a t;
                                        Ir.MemBlock.c := Ir.MemBlock.c t;
                                        Ir.MemBlock.P := Ir.MemBlock.P t |}) in Hgetb1'.
                  inv Hgetb1'.
                  simpl. reflexivity.
                  { eapply Ir.Memory.incr_time_wf. eapply wf_m. reflexivity. }
                  { eassumption. }
                  { rewrite Ir.Memory.get_incr_time_id. eassumption. }
                  { reflexivity. }
                }
                { rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time (Ir.Config.m st))
                      (mb := t0) (mb' := {|
                                          Ir.MemBlock.bt := Ir.MemBlock.bt t;
                                          Ir.MemBlock.r := (fst (Ir.MemBlock.r t),
                                                            Some (Ir.Memory.mt (Ir.Config.m st)));
                                          Ir.MemBlock.n := Ir.MemBlock.n t;
                                          Ir.MemBlock.a := Ir.MemBlock.a t;
                                          Ir.MemBlock.c := Ir.MemBlock.c t;
                                          Ir.MemBlock.P := Ir.MemBlock.P t |})
                      (bid' := b) in Hgetb1'.
                  inv Hgetb1'.
                  unfold Ir.MemBlock.alive in Halivet.
                  destruct (Ir.MemBlock.r t) eqn:Htr.
                  simpl in Halivet. destruct o; try congruence.
                  destruct (Ir.MemBlock.r blk0') eqn:Hrblk0'.
                  destruct o.
                  { simpl. destruct wf_m.
                    assert (fst (Ir.MemBlock.r blk0') < Ir.Memory.mt (Ir.Config.m st)).
                    { eapply wf_blocktime. symmetry in Hgetb1. eapply Ir.Memory.get_In in Hgetb1.
                      eapply Hgetb1. reflexivity. }
                    rewrite Hrblk0' in H0. SearchAbout (PeanoNat.Nat.ltb).
                    simpl in H0.
                    assert (~ Ir.Memory.mt (Ir.Config.m st) < t1).
                    { intros HH. omega. }
                    rewrite <- Nat.ltb_nlt in H1.
                    rewrite H1. simpl. reflexivity.
                  }
                  { simpl. destruct wf_m.
                    assert (fst (Ir.MemBlock.r blk0') < Ir.Memory.mt (Ir.Config.m st)).
                    { eapply wf_blocktime. symmetry in Hgetb1. eapply Ir.Memory.get_In in Hgetb1.
                      eapply Hgetb1. reflexivity. }
                    rewrite Hrblk0' in H0. SearchAbout (PeanoNat.Nat.ltb).
                    simpl in H0.
                    assert (~ Ir.Memory.mt (Ir.Config.m st) < t1).
                    { intros HH. omega. }
                    rewrite <- Nat.ltb_nlt in H1.
                    rewrite H1. simpl. reflexivity.
                  }
                  { eapply Ir.Memory.incr_time_wf. apply wf_m. reflexivity. }
                  { eassumption. }
                  { erewrite Ir.Memory.get_incr_time_id. assumption. }
                  { reflexivity. }
                  { rewrite PeanoNat.Nat.eqb_neq in HBB0. omega. }
                }
              }
              { eapply Ir.Memory.incr_time_wf. apply wf_m. reflexivity. }
              { eassumption. }
              { erewrite Ir.Memory.get_incr_time_id. assumption. }
              { inv HFREE. reflexivity. }
            }
            { (* okay, freed block l is different from b. *)
              destruct (l =? b0) eqn:HLB0.
              { rewrite PeanoNat.Nat.eqb_eq in HLB0.
                subst l.
                rewrite Nat.eqb_sym in HLB.
                rewrite HLB. simpl.
                unfold Ir.Memory.free in HFREE.
                rewrite Hgetb1 in HFREE.
                destruct (Ir.MemBlock.bt t0) eqn:HBT0; try congruence.
                destruct (Ir.MemBlock.set_lifetime_end t0 (Ir.Memory.mt (Ir.Config.m st))) eqn:HLIFETIME0;
                  try congruence.
                { 
                  unfold Ir.MemBlock.set_lifetime_end in HLIFETIME0.
                  destruct (Ir.MemBlock.alive t0) eqn:HALIVE0; try congruence.
                  inv HLIFETIME0.
                  inv HFREE.
                  rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time (Ir.Config.m st))
                                                      (bid' := b0) (mb := t) (mb' := {|
                                                                                      Ir.MemBlock.bt := Ir.MemBlock.bt t0;
                                                                                      Ir.MemBlock.r := (fst (Ir.MemBlock.r t0), Some (Ir.Memory.mt (Ir.Config.m st)));
                                                                                      Ir.MemBlock.n := Ir.MemBlock.n t0;
                                                                                      Ir.MemBlock.a := Ir.MemBlock.a t0;
                                                                                      Ir.MemBlock.c := Ir.MemBlock.c t0;
                                                                                      Ir.MemBlock.P := Ir.MemBlock.P t0 |}) in Hgetb'.
                  inv Hgetb'.
                  unfold Ir.MemBlock.alive in HALIVE0.
                  destruct (Ir.MemBlock.r t0) eqn:HRT0.
                  simpl in HALIVE0. destruct o; try congruence.
                  destruct (Ir.MemBlock.r blk') eqn:Hrblk'.
                  rewrite Ir.Memory.get_set_id with (m := Ir.Memory.incr_time (Ir.Config.m st))
                                                    (mb := t0)
                                                    (mb' := {|
                                                             Ir.MemBlock.bt := Ir.MemBlock.bt t0;
                                                             Ir.MemBlock.r := (fst (t, @None nat),
                                                                               Some (Ir.Memory.mt (Ir.Config.m st)));
                                                             Ir.MemBlock.n := Ir.MemBlock.n t0;
                                                             Ir.MemBlock.a := Ir.MemBlock.a t0;
                                                             Ir.MemBlock.c := Ir.MemBlock.c t0;
                                                             Ir.MemBlock.P := Ir.MemBlock.P t0 |}) in Hgetb1'.
                  inv Hgetb1'.
                  simpl.
                  destruct o.
                  {
                    (* blk' has (_, Some) *)
                    destruct wf_m.
                    assert (fst (Ir.MemBlock.r blk') < Ir.Memory.mt (Ir.Config.m st)).
                    { eapply wf_blocktime. symmetry in Hgetb. eapply Ir.Memory.get_In in Hgetb.
                      eapply Hgetb. reflexivity. }
                    rewrite Hrblk' in H0.
                    simpl in H0.
                    assert (~ Ir.Memory.mt (Ir.Config.m st) < t1).
                    { intros HH. omega. }
                    rewrite <- Nat.ltb_nlt in H1.
                    rewrite H1. simpl. rewrite orb_false_r. reflexivity.
                  }
                  { (* blk' has (_, None) lifetime *)
                    destruct wf_m.
                    assert (fst (Ir.MemBlock.r blk') < Ir.Memory.mt (Ir.Config.m st)).
                    { eapply wf_blocktime. symmetry in Hgetb. eapply Ir.Memory.get_In in Hgetb.
                      eapply Hgetb. reflexivity. }
                    rewrite Hrblk' in H0.
                    simpl in H0.
                    assert (~ Ir.Memory.mt (Ir.Config.m st) < t1).
                    { intros HH. omega. }
                    rewrite <- Nat.ltb_nlt in H1.
                    rewrite H1. simpl. rewrite orb_false_r. reflexivity.
                  } 
                  { eapply Ir.Memory.incr_time_wf. eapply wf_m. reflexivity. }
                  { assumption. }
                  { rewrite Ir.Memory.get_incr_time_id. assumption. }
                  { reflexivity. }
                  { eapply Ir.Memory.incr_time_wf. eapply wf_m. reflexivity. }
                  { assumption. }
                  { rewrite Ir.Memory.get_incr_time_id. assumption. }
                  { reflexivity. }
                  { rewrite PeanoNat.Nat.eqb_neq in HLB. congruence. }
                }
                { unfold Ir.MemBlock.set_lifetime_end in HLIFETIME0.
                  des_ifs.
                }
              }
              { (* freed block l is diferent from both b and b0! *)
                rewrite PeanoNat.Nat.eqb_neq in HLB, HLB0.
                unfold Ir.Memory.free in HFREE.
                destruct (Ir.Memory.get (Ir.Config.m st) l) eqn:Hgetl; try congruence.
                destruct (Ir.MemBlock.bt t1) eqn:Hbtt1; try congruence.
                destruct (Ir.MemBlock.alive t1) eqn:Halivet1; try congruence.
                destruct (Ir.MemBlock.set_lifetime_end t1 (Ir.Memory.mt (Ir.Config.m st))) eqn:Hlifetimet1;
                  try congruence.
                simpl in *.
                inv HFREE.
                rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time (Ir.Config.m st))
                                                    (bid' := l) (mb := t) (mb' := t2) in Hgetb'.
                inv Hgetb'.
                rewrite Ir.Memory.get_set_diff with (m := Ir.Memory.incr_time (Ir.Config.m st))
                                                    (bid' := l) (mb := t0) (mb' := t2) in Hgetb1'.
                inv Hgetb1'.
                reflexivity.
                { eapply Ir.Memory.incr_time_wf. eapply wf_m. reflexivity. }
                { assumption. }
                { rewrite Ir.Memory.get_incr_time_id. assumption. }
                { reflexivity. }
                { congruence. }
                { eapply Ir.Memory.incr_time_wf. eapply wf_m. reflexivity. }
                { assumption. }
                { rewrite Ir.Memory.get_incr_time_id. assumption. }
                { reflexivity. }
                { congruence. }
              }
            }
          }
          assumption. congruence.
        }
        { (* Ir.Memory.get (Ir.Config.m st) b0 = None *)
          assert (H0:Ir.Memory.get m' b0 = None).
          { eapply Ir.Memory.get_free_none. apply wf_m.
            eassumption. eassumption. }
          rewrite H0. reflexivity.
        }
        assumption. congruence.
      }
      { (*( Ir.Memory.get (Ir.Config.m st) b = None *)
        assert (H0:Ir.Memory.get m' b = None).
        { eapply Ir.Memory.get_free_none. apply wf_m.
          eassumption. eassumption. }
        rewrite H0. reflexivity.
      }
    }
    reflexivity.
  }
  { reflexivity. }
Qed.

(* Lemma: Ir.SmallStep.icmp_eq_ptr returns unchanged value even
   if Memory.free is called *)
Lemma icmp_eq_ptr_free_invariant:
  forall md st op1 op2 p1 p2 m' l
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.icmp_eq_ptr p1 p2 m' =
    Ir.SmallStep.icmp_eq_ptr p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr.
  destruct p1.
  { destruct p2.
    { destruct (b =? b0); try reflexivity.
      erewrite icmp_eq_ptr_nondet_cond_free_invariant. reflexivity.
      eassumption. eassumption. eassumption. eassumption. }
    { erewrite p2N_free_invariant. reflexivity.
      eassumption. eassumption. eassumption. }
  }
  { destruct p2; try (unfold Ir.SmallStep.p2N; reflexivity).
    erewrite p2N_free_invariant. reflexivity. eassumption. eassumption. eassumption.
  }
Qed.

Theorem reorder_free_icmp_eq:
  forall i1 i2 r2 (opptr1 op21 op22:Ir.op) opty2
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.iicmp_eq r2 opty2 op21 op22),
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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    {
      rewrite incrpc_update_m in HNEXT.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite Ir.Config.cur_inst_update_m in HNEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite HLOCATE2 in HNEXT.
      repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
      repeat (rewrite get_val_incrpc in HNEXT).
      des_ifs; try(
                   eexists; split;
                   [ eapply Ir.SmallStep.ns_success;
                     [ eapply Ir.SmallStep.ns_one;
                       eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite HLOCATE1';
                       rewrite Heq1; try rewrite Heq2; reflexivity
                     | eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite cur_inst_update_reg_and_incrpc;
                       apply incrpc'_incrpc in HLOCATE_NEXT';
                       rewrite HLOCATE_NEXT' in HLOCATE2';
                       rewrite HLOCATE2';
                       get_val_independent_goal opptr1 r2;
                       rewrite Heq;
                       rewrite m_update_reg_and_incrpc;
                       rewrite Heq0;
                       reflexivity ]
                   | rewrite nstep_eq_trans_3;
                     apply nstep_eq_refl
                   ]
                 ).
      { eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            rewrite Heq1. rewrite Heq2.
            rewrite m_update_m in Heq3.
            assert (HPTR:Ir.SmallStep.icmp_eq_ptr p0 p1 (Ir.Config.m st) =
                         Ir.SmallStep.icmp_eq_ptr p0 p1 t).
            { unfold Ir.SmallStep.free in Heq0.
              des_ifs.
              erewrite <- icmp_eq_ptr_free_invariant. reflexivity. eassumption.
              eassumption. eassumption. symmetry in Heq0. eapply Heq0.
              erewrite <- icmp_eq_ptr_free_invariant. reflexivity. eassumption.
              eassumption. eassumption. symmetry in Heq0. eapply Heq0.
            }
            rewrite HPTR, Heq3. reflexivity.
          }
          { eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq.
            rewrite m_update_reg_and_incrpc.
            rewrite Heq0.
            reflexivity.
          }
        }
        { rewrite nstep_eq_trans_3;
            apply nstep_eq_refl.
        }
      }
    }
    { (* icmp nondet *)
      apply incrpc'_incrpc in HLOCATE_NEXT.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite cur_inst_incrpc_update_m in HCUR.
      rewrite HLOCATE2 in HCUR.
      inv HCUR.
      rewrite get_val_incrpc in HOP1.
      rewrite get_val_incrpc in HOP2.
      rewrite Ir.Config.get_val_update_m in HOP1.
      rewrite Ir.Config.get_val_update_m in HOP2.
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        { eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_eq_nondet; try reflexivity.
          rewrite HLOCATE1'. reflexivity. eassumption. eassumption.
          rewrite incrpc_update_m in HNONDET.
          rewrite m_update_m in HNONDET.
          assert (HPTR:Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st) =
                       Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 t).
          { unfold Ir.SmallStep.free in Heq0.
            des_ifs.
            erewrite <- icmp_eq_ptr_nondet_cond_free_invariant.
            eassumption. eassumption. eauto. eauto. eauto.
            erewrite <- icmp_eq_ptr_nondet_cond_free_invariant.
            eassumption. eassumption. eauto. eauto. eauto.
          }
          rewrite HPTR. assumption.
        }
        { eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite cur_inst_update_reg_and_incrpc.
          apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite HLOCATE2'.
          get_val_independent_goal opptr1 r2.
          rewrite Heq.
          rewrite m_update_reg_and_incrpc.
          rewrite Heq0.
          reflexivity.
        }
      }
      { rewrite incrpc_update_m.
        rewrite nstep_eq_trans_3.
        eapply nstep_eq_refl.
      }
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
      des_ifs.
      {
        assert (HSUCC := icmp_eq_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_eq_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. rewrite m_update_reg_and_incrpc.
            rewrite Heq0. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_eq_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_eq_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
    + inv HSUCC.
    + inv HGW0.
Admitted.


(********************************************
   REORDERING of icmp_eq - free:

   r1 = iicmp_eq opty1 op11 op12
   free opptr2
   ->
   free opptr2
   r1 = iicmp_eq opty1 op11 op12
**********************************************)

Theorem reorder_icmp_eq_free:
  forall i1 i2 r1 (op11 op12 opptr2:Ir.op) opty1
         (HINST1:i1 = Ir.Inst.iicmp_eq r1 opty1 op11 op12)
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
    (*
    (* exploit that iicmp always succeeds, with update_reg_and_incrpc..! *)
    exploit icmp_eq_always_succeeds2.
    + eapply HLOCATE1.
    + eapply HSINGLE0.
    + intros HSUCCEED.
    destruct HSUCCEED as [vtmp HSUCCEED]. inv HSUCCEED.
    *)
    inv HSINGLE0; try congruence.
    { (* icmp det *)
      unfold_det HNEXT HLOCATE1.
      des_ifs;
        inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                          rewrite HLOCATE2 in HCUR; congruence);
        try (
            (* icmp int , int / int , poison / .. *)
            (* free deterministic. *)
            unfold_det HNEXT HLOCATE2;
            get_val_independent_H HNEXT opptr2 r1;
            rewrite m_update_reg_and_incrpc in HNEXT;
            des_ifs; try
                       ( (* free went wrong. *)
                         eexists; split;
                         [ eapply Ir.SmallStep.ns_goes_wrong;
                           eapply Ir.SmallStep.ns_one;
                           eapply Ir.SmallStep.s_det;
                           unfold Ir.SmallStep.inst_det_step;
                           rewrite HLOCATE1';
                           try rewrite Heq0; try rewrite Heq1;
                           try rewrite Heq2; try rewrite Heq3; reflexivity
                         | constructor; reflexivity ]
                       );
            ( (* free succeed. *)
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ eapply Ir.SmallStep.ns_one;
                  eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite HLOCATE1';
                  try rewrite Heq0; try rewrite Heq1;
                  try rewrite Heq2; try rewrite Heq3; reflexivity
                | eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_incrpc_update_m;
                  rewrite HLOCATE2';
                  repeat (rewrite get_val_incrpc);
                  repeat (rewrite Ir.Config.get_val_update_m);
                  rewrite Heq; try rewrite Heq0; reflexivity
                ]
              | rewrite <- nstep_eq_trans_3;
                rewrite incrpc_update_m;
                apply nstep_eq_refl
              ]
            )
          ).
      { (* icmp_eq_ptr succeeds *)
        unfold_det HNEXT HLOCATE2.
        get_val_independent_H HNEXT opptr2 r1.
        rewrite m_update_reg_and_incrpc in HNEXT.
        des_ifs;
          try ( (* free went wrong. *)
              eexists; split;
              [ eapply Ir.SmallStep.ns_goes_wrong;
                eapply Ir.SmallStep.ns_one;
                eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                rewrite HLOCATE1';
                try rewrite Heq1; try rewrite Heq2; try rewrite Heq3; reflexivity
              | constructor; reflexivity ]
            ).
        { (* free succeed. *)
          eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite HLOCATE1'.
              try rewrite Heq1; try rewrite Heq2; rewrite Heq3. reflexivity.
            }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'.
              repeat (rewrite get_val_incrpc).
              repeat (rewrite Ir.Config.get_val_update_m).
              rewrite Heq, Heq0.
              rewrite incrpc_update_m.
              rewrite m_update_m.
              assert (HPTR:Ir.SmallStep.icmp_eq_ptr p p0 t =
                           Ir.SmallStep.icmp_eq_ptr p p0 (Ir.Config.m st)).
              { unfold Ir.SmallStep.free in Heq3. des_ifs;
                erewrite <- icmp_eq_ptr_free_invariant; try eauto. }
              rewrite HPTR. rewrite Heq1.
              reflexivity.
            }
          }
          { rewrite <- nstep_eq_trans_3.
            apply nstep_eq_refl.
          }
        }
      }
    }
    { (* icmp nondet *)
      inv HSINGLE; try (
        rewrite cur_inst_update_reg_and_incrpc in HCUR0;
        rewrite HLOCATE2 in HCUR0; congruence).
      (* getting free cases by destruct.. *)
      unfold_det HNEXT HLOCATE2.
      get_val_independent_H HNEXT opptr2 r.
      rewrite m_update_reg_and_incrpc in HNEXT.
      rewrite HLOCATE1 in HCUR. inv HCUR.
      symmetry in HNEXT.
      des_ifs; try
      ( (* free went wrong. *)
        eexists; split;
        [ eapply Ir.SmallStep.ns_goes_wrong;
            eapply Ir.SmallStep.ns_one;
            eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite HLOCATE1'; rewrite Heq; try rewrite Heq0; reflexivity 
        | constructor; reflexivity ]).
      { (* free succeed. *)
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            rewrite Heq. rewrite Heq0. reflexivity.
          }
          { eapply Ir.SmallStep.s_icmp_eq_nondet.
            { rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'. reflexivity. }
            { reflexivity. }
            { rewrite get_val_incrpc_update_m.
              eassumption. }
            { rewrite get_val_incrpc_update_m.
              eassumption. }
            { rewrite m_incrpc_update_m.
              assert (HNONDETCND:
                        Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 t =
                        Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
              { unfold Ir.SmallStep.free in Heq0.
                des_ifs; erewrite icmp_eq_ptr_nondet_cond_free_invariant; eauto. }
              rewrite HNONDETCND.
              eassumption. }
          }
        }
        { rewrite <- nstep_eq_trans_3.
          rewrite incrpc_update_m.
          apply nstep_eq_refl.
        }
      }
    }
  - (* icmp never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iicmp_eq r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* inttoptr never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iicmp_eq r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of malloc - icmp_ule:

   r1 = malloc ty opptr1
   r2 = icmp_ule opty2 op21 op22
   ->
   r2 = icmp_ule opty2 op21 op22
   r1 = malloc ty opptr1.
**********************************************)

Lemma icmp_ule_always_succeeds:
  forall st (md:Ir.IRModule.t) r opty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r opty op1 op2)),
  exists st' v,
    (Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success Ir.e_none st') /\
    (st' = Ir.SmallStep.update_reg_and_incrpc md st r v)).
Proof.
  intros.
  destruct (Ir.Config.get_val st op1) eqn:Hop1.
  { destruct v.
    { (* op1 is number *)
      destruct (Ir.Config.get_val st op2) eqn:Hop2.
      { destruct v;
          try (eexists; eexists; split;
          [ eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
              rewrite HCUR; rewrite Hop1, Hop2; reflexivity
          | reflexivity ]).
      }
      { eexists. eexists. split.
        { eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
          rewrite HCUR; rewrite Hop1, Hop2. reflexivity. }
        { reflexivity. }
      }
    }
    { destruct (Ir.Config.get_val st op2) eqn:Hop2.
      { destruct v.
        { eexists. eexists. split.
          { eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
              rewrite HCUR; rewrite Hop1, Hop2. reflexivity. }
          { reflexivity. } }
        { destruct (Ir.SmallStep.icmp_ule_ptr_nondet_cond p p0 (Ir.Config.m st))
            eqn:HDET.
          { eexists. eexists. split.
            { eapply Ir.SmallStep.s_icmp_ule_nondet.
              rewrite HCUR. reflexivity.
              reflexivity. rewrite Hop1. reflexivity.
              rewrite Hop2. reflexivity.
              eassumption. }
            { reflexivity. }
          }
          { destruct p; destruct p0; try (
              eexists; eexists; split;
              [ eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                unfold Ir.SmallStep.icmp_ule_ptr;
                rewrite HCUR, Hop1, Hop2; reflexivity
              | reflexivity]; fail).
            { destruct (PeanoNat.Nat.leb n n0) eqn:HEQB; try (
                eexists; eexists; split; 
                [ eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  unfold Ir.SmallStep.icmp_ule_ptr;
                  rewrite HCUR, Hop1, Hop2, HDET, HEQB; reflexivity
                | reflexivity ] ).
            }
          }
        }
        { eexists. eexists. split.
          { eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite HCUR, Hop1, Hop2; reflexivity. }
          { reflexivity. }
        }
      }
      { eexists. eexists. split.
        { eapply Ir.SmallStep.s_det;
          unfold Ir.SmallStep.inst_det_step;
          rewrite HCUR, Hop1, Hop2; reflexivity. }
        { reflexivity. }
      }
    }
    { eexists. eexists. split.
      { eapply Ir.SmallStep.s_det;
        unfold Ir.SmallStep.inst_det_step;
        rewrite HCUR, Hop1; reflexivity. }
      { reflexivity. }
    }
  }
  { eexists. eexists. split.
    { eapply Ir.SmallStep.s_det.
      unfold Ir.SmallStep.inst_det_step.
      rewrite HCUR. rewrite Hop1. reflexivity. }
    { reflexivity. }
  }
  (* Why should I do this? *) Unshelve. constructor.
Qed.

Lemma icmp_ule_always_succeeds2:
  forall st st' (md:Ir.IRModule.t) r opty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r opty op1 op2))
         (HSTEP: Ir.SmallStep.inst_step md st st'),
  exists v, st' = Ir.SmallStep.sr_success Ir.e_none
                                (Ir.SmallStep.update_reg_and_incrpc md st r v).
Proof.
  intros.
  inv HSTEP; try congruence.
  { unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    destruct (Ir.Config.get_val st op1) eqn:Hop1.
    { destruct v.
      { (* op1 is number *)
        destruct (Ir.Config.get_val st op2) eqn:Hop2.
        { des_ifs; eexists; reflexivity. }
        { inv HNEXT; eexists; reflexivity. }
      }
      { (* op1 is ptr *)
        destruct (Ir.Config.get_val st op2) eqn:Hop2.
        { des_ifs; eexists; reflexivity. }
        { inv HNEXT; eexists; reflexivity. }
      }
      { inv HNEXT. eexists. reflexivity. }
    }
    { inv HNEXT. eexists. reflexivity. }
  }
  { rewrite HCUR in HCUR0. inv HCUR0.
    eexists. reflexivity. }
Qed.

Lemma icmp_ule_ptr_nondet_cond_new_invariant:
  forall md l m' p1 p2 st nsz contents P op1 op2
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m (Ir.Config.update_m st m')) =
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
  destruct p1.
  { destruct p2.
    { erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
        try reflexivity;
        try (destruct HWF; eassumption);
        try (try rewrite m_update_m; eassumption).
      destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:HGETB.
      { destruct HWF. apply wf_no_bogus_ptr in HGV1. assumption. }
      { destruct HWF. apply wf_no_bogus_ptr in HGV1. assumption. }
    }
    { reflexivity. }
  }
  { destruct p2.
    { reflexivity. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
Qed.

Lemma icmp_ule_ptr_new_invariant:
  forall md l m' p1 p2 st nsz contents P op1 op2
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.icmp_ule_ptr p1 p2 (Ir.Config.m (Ir.Config.update_m st m')) =
    Ir.SmallStep.icmp_ule_ptr p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr.
  erewrite icmp_ule_ptr_nondet_cond_new_invariant.
  destruct (Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st)) eqn:HNONDET; try reflexivity.
  destruct p1.
  { destruct p2.
    { destruct (b =? b0) eqn:Heqb.
      {
        erewrite Ir.Memory.get_new with (m := Ir.Config.m st);
          try reflexivity;
          try (destruct HWF; eassumption);
          try (try rewrite m_update_m; eassumption).
        destruct HWF. apply wf_no_bogus_ptr in HGV1. assumption.
      }
      { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET.
        rewrite Heqb in HNONDET. inv HNONDET.
      }
    }
    { erewrite p2N_new_invariant; try eassumption. reflexivity. }
  }
  { destruct p2.
    { erewrite p2N_new_invariant;try eassumption. reflexivity. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
Qed.


Theorem reorder_malloc_icmp_ule:
  forall i1 i2 r1 r2 (opptr1 op21 op22:Ir.op) ty1 opty2
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.iicmp_ule r2 opty2 op21 op22),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* malloc succeeds. *)
    inv HSUCC; try (inv HSUCC0; fail).
    exploit inst_step_incrpc. eapply HLOCATE_NEXT. eapply HSINGLE0.
    intros HCUR'.
    inv HSINGLE; try congruence.
    + (* iicmp works deterministically. *)
      unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite <- HCUR' in HNEXT.
      rewrite HLOCATE2 in HNEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      (* now get malloc's behavior *)
      inv HSINGLE0; try congruence.
      * unfold Ir.SmallStep.inst_det_step in HNEXT0. rewrite HLOCATE1 in HNEXT0.
        congruence.
      * (* Malloc returned NULL. *)
        inv_cur_inst HCUR HLOCATE1.
        rewrite get_val_independent2 in HNEXT.
        rewrite get_val_independent2 in HNEXT.
        rewrite m_update_reg_and_incrpc in HNEXT.
        destruct (Ir.Config.get_val st op21) eqn:Hop21;
          destruct (Ir.Config.get_val st op22) eqn:Hop22.
        { destruct v; destruct v0; try inv HNEXT;
          try (eexists; split;
          [ eapply Ir.SmallStep.ns_success;
            [ eapply Ir.SmallStep.ns_one;
              inst_step_det_trivial HLOCATE1' Hop21 Hop22
            | s_malloc_null_trivial HLOCATE2';
              get_val_independent_goal opptr1 r2]
          | eapply nstep_eq_trans_1;
            [ assert (r1 <> r2) by admit; assumption | apply nstep_eq_refl ] ]).
          - des_ifs. eexists. split.
            + eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
              inst_step_icmp_det_ptr_trivial HLOCATE1' Hop21 Hop22 Heq.
              s_malloc_null_trivial HLOCATE2'.
            + eapply nstep_eq_trans_1. assert (r1 <> r2) by admit.
              assumption. apply nstep_eq_refl.
        }
        { destruct v; try inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
        }
        { destruct op22. congruence. assert (r <> r1) by admit. congruence. }
        { destruct op21. congruence. assert (r <> r1) by admit. congruence. }
      * (* malloc succeeded. *)
        get_val_independent_H HNEXT op21 r.
        get_val_independent_H HNEXT op22 r.
        inv_cur_inst HCUR HLOCATE1.
        repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
        des_ifs; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success;
            [ apply Ir.SmallStep.ns_one;
              try inst_step_det_trivial HLOCATE1' Heq Heq0;
              try (rewrite m_update_reg_and_incrpc in Heq1;
                   inst_step_icmp_det_ptr_trivial HLOCATE1' Heq Heq0 Heq1)
            | s_malloc_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_2; [ assert (r2 <> r1) by admit; congruence 
            | apply nstep_eq_refl ]]).
        { eexists. split.
          { eapply Ir.SmallStep.ns_success.
            - apply Ir.SmallStep.ns_one.
              rewrite m_update_reg_and_incrpc in Heq1.
              apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
              rewrite HLOCATE1'. rewrite Heq. rewrite Heq0.
              rewrite m_update_m in Heq1.
              assert (HPTR:Ir.SmallStep.icmp_ule_ptr p p0 (Ir.Config.m st) =
                           Ir.SmallStep.icmp_ule_ptr p p0 m').
              { erewrite <- icmp_ule_ptr_new_invariant. rewrite m_update_m. reflexivity.
                eassumption. eassumption. eassumption. eassumption. eassumption.
                eassumption. eassumption. }
              rewrite HPTR. rewrite Heq1. reflexivity.
            - s_malloc_trivial HLOCATE2'. get_val_independent_goal opptr1 r2.
          }
          { eapply nstep_eq_trans_2; [ assert (r2 <> r1) by admit; congruence 
            | apply nstep_eq_refl ]. }
        }
    + (* icmp works nondeterministically. *)
      inv HSINGLE0; try congruence;
        try (unfold Ir.SmallStep.inst_det_step in HNEXT;
             rewrite HLOCATE1 in HNEXT; congruence).
      * rewrite m_update_reg_and_incrpc in *.
        inv_cur_inst HCUR0 HLOCATE1.
        rewrite <- HCUR' in HCUR.
        inv_cur_inst HCUR HLOCATE2.
        get_val_independent_H HOP1 op21 r1.
        get_val_independent_H HOP2 op22 r1.
        eexists. split.
        { eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_ule_nondet.
          rewrite HLOCATE1'. reflexivity.
          reflexivity. eapply HOP1. eapply HOP2. eassumption.
          apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          s_malloc_null_trivial HLOCATE2'.
        }
        { eapply nstep_eq_trans_1.
          { assert (r1 <> r2). admit. congruence. } 
          { apply nstep_eq_refl. }
        }
      * rewrite m_update_reg_and_incrpc in *.
        rewrite cur_inst_update_reg_and_incrpc in *.
        repeat (rewrite m_update_m in *).
        inv_cur_inst_next HCUR' HLOCATE2' HLOCATE_NEXT'.
        inv_cur_inst_next HCUR HLOCATE2 HLOCATE_NEXT.
        inv_cur_inst HCUR0 HLOCATE1.
        get_val_independent_H HOP1 op21 r1.
        get_val_independent_H HOP2 op22 r1.
        eexists. split.
        { eapply Ir.SmallStep.ns_success. eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_ule_nondet.
          rewrite HLOCATE1'. reflexivity.
          reflexivity. eapply HOP1. eapply HOP2.
          assert (HCMP: Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 m' =
                        Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
          { erewrite <- icmp_ule_ptr_nondet_cond_new_invariant. rewrite m_update_m.
            reflexivity.
            eassumption. eauto. eauto. eauto. eauto. eauto. eauto. }
          rewrite <- HCMP. assumption.
          s_malloc_trivial HLOCATE2'.
          get_val_independent_goal opptr1 r2.
        }
        { eapply nstep_eq_trans_2.
          assert (r2 <> r1). admit. congruence.
          eapply nstep_eq_refl. }
  - (* malloc raised oom. *)
    inv HOOM.
    + inv HSINGLE. unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. inv HNEXT.
      inv_cur_inst HCUR HLOCATE1.
      (* icmp only succeeds. *)
      assert (HSUCC := icmp_ule_always_succeeds st md' r2 opty2
                                                   op21 op22 HLOCATE1').
      destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        - eapply Ir.SmallStep.ns_one.
          eapply HSUCC1.
        - eapply Ir.SmallStep.s_malloc_oom.
          rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
          reflexivity.
          reflexivity.
          rewrite HSUCC2. get_val_independent_goal opptr1 r2.
          rewrite HSUCC2. rewrite m_update_reg_and_incrpc. eassumption.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HOOM0.
  - (* malloc never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.imalloc r1 ty1 opptr1)).
      reflexivity. eapply HLOCATE1. eassumption.
      intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of icmp_ule - malloc:

   r1 = icmp_ule opty1 op11 op12
   r2 = malloc ty2 opptr2
   ->
   r2 = malloc ty2 opptr2
   r1 = icmp_ule opty1 op11 op12
**********************************************)

Theorem reorder_icmp_ule_malloc:
  forall i1 i2 r1 r2 (op11 op12 opptr2:Ir.op) opty1 ty2
         (HINST1:i1 = Ir.Inst.iicmp_ule r1 opty1 op11 op12)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* icmp - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      {
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT. inv HNEXT.
        des_ifs;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ eapply Ir.SmallStep.ns_one;
                  s_malloc_null_trivial HLOCATE1';
                  get_val_independent_H HZERO opptr2 r1
                | eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite HLOCATE2';
                  get_val_independent_goal op11 r2;
                  rewrite Heq;
                  try (get_val_independent_goal op12 r2;
                       rewrite Heq0);
                  reflexivity ]
              | rewrite nstep_eq_trans_1;
                [ apply nstep_eq_refl | assert (r1 <> r2) by admit; congruence ] ]).
        { eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_null_trivial HLOCATE1'.
            }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Heq.
              get_val_independent_goal op12 r2.
              rewrite Heq0.
              rewrite m_update_reg_and_incrpc.
              rewrite Heq1.
              reflexivity.
            }
          }
          { rewrite nstep_eq_trans_1. apply nstep_eq_refl.
            assert (r1 <> r2). admit. congruence. }
        }
      }
      { rewrite HLOCATE1 in HCUR. inv HCUR.
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            s_malloc_null_trivial HLOCATE1'.
          }
          { eapply Ir.SmallStep.s_icmp_ule_nondet.
            rewrite cur_inst_update_reg_and_incrpc.
            rewrite HLOCATE2'. reflexivity.
            reflexivity.
            get_val_independent_goal op11 r2.
            get_val_independent_goal op12 r2.
            rewrite m_update_reg_and_incrpc.
            assumption.
          }
        }
        { rewrite nstep_eq_trans_1. apply nstep_eq_refl.
          assert (r1 <> r2). admit. congruence. }
      }
    + (* oom *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply icmp_ule_always_succeeds2 with (r := r1) (opty := opty1)
          (op1 := op11) (op2 := op12) in HSINGLE0.
      destruct HSINGLE0 as [vtmp HSINGLE0]. inv HSINGLE0.
      eexists (nil, Ir.SmallStep.sr_oom).
      split.
      { eapply Ir.SmallStep.ns_oom.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc_oom.
        rewrite HLOCATE1'. reflexivity. reflexivity.
        get_val_independent_H HSZ opptr2 r1. eassumption.
        rewrite m_update_reg_and_incrpc in HNOSPACE.
        assumption.
      }
      { constructor. reflexivity. }
      assumption.
    + (* malloc succeeds *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      { (* icmp is determinsitic *)
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT.
        des_ifs;
          rewrite m_update_reg_and_incrpc in *;
          rewrite cur_inst_update_reg_and_incrpc in *;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ (* malloc *)
                  eapply Ir.SmallStep.ns_one;
                  eapply Ir.SmallStep.s_malloc; try (eauto; fail);
                  try eassumption;
                  try get_val_independent_H HSZ opptr2 r1
                | (* icmp, det *)
                  eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite cur_inst_incrpc_update_m;
                  rewrite HLOCATE2';
                  get_val_independent_goal op11 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq;
                  try (get_val_independent_goal op12 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq0);
                  reflexivity
                ]
              | eapply nstep_eq_trans_2;
                [ assert (r1 <> r2) by admit; assumption
                | apply nstep_eq_refl ]
              ]).
        { (* icmp ptr deterministic *)
          eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_trivial HLOCATE1'.
              get_val_independent_H HSZ opptr2 r1. }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Ir.Config.get_val_update_m, Heq.
              get_val_independent_goal op12 r2.
              rewrite Ir.Config.get_val_update_m, Heq0.
              rewrite m_update_reg_and_incrpc.
              rewrite m_update_m.
              assert (HPTR:Ir.SmallStep.icmp_ule_ptr p p0 m' =
                           Ir.SmallStep.icmp_ule_ptr p p0 (Ir.Config.m st)).
              admit.
              rewrite HPTR. rewrite Heq1. reflexivity.
            }
          }
          {
            rewrite nstep_eq_trans_2.
            { apply nstep_eq_refl. }
            { assert (r1 <> r2) by admit. congruence. }
          }
        }
      }
      { (* icmp non-det. *)
        rewrite HLOCATE1 in HCUR. inv HCUR.
        rewrite m_update_reg_and_incrpc in *.
        eexists.
        split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            s_malloc_trivial HLOCATE1'.
            get_val_independent_H HSZ opptr2 r1.
          }
          { eapply Ir.SmallStep.s_icmp_ule_nondet.
            { rewrite cur_inst_update_reg_and_incrpc.
              rewrite cur_inst_incrpc_update_m.
              eauto. }
            { reflexivity. }
            { get_val_independent_goal op11 r2. }
            { get_val_independent_goal op12 r2. }
            { rewrite m_update_reg_and_incrpc.
              rewrite m_update_m.
              assert (Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 m' =
                      Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
              { erewrite <- icmp_ule_ptr_nondet_cond_new_invariant.
                rewrite m_update_m. reflexivity.
                eauto. eauto. eauto. eauto. eauto. eauto. eauto. }
              congruence. }
          }
        }
        { rewrite nstep_eq_trans_2.
          apply nstep_eq_refl.
          assert (r1 <> r2). admit. congruence. }
      }
  - (* icmp never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iicmp_ule r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* icmp never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iicmp_ule r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of free - icmp_ule:

   free opptr1
   r2 = icmp_ule opty2 op21 op22
   ->
   r2 = icmp_ule opty2 op21 op22
   free opptr1
**********************************************)

(* Lemma: Ir.SmallStep.icmp_ule_ptr_nondet_cond returns unchanged value even
   if Memory.free is called *)
Lemma icmp_ule_ptr_nondet_cond_free_invariant:
  forall md st op1 op2 p1 p2 m' l
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 m' =
    Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st).
Proof.
  intros.
  destruct HWF.
  assert (Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
  destruct p1; try reflexivity.
  destruct p2; try reflexivity.
  destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:Hgetb.
  { dup Hgetb. apply Ir.Memory.get_free_some with (m' := m') (l0 := l) in Hgetb0.
    destruct Hgetb0 as [blk' Hgetb'].
    rewrite Hgetb'.

    rewrite get_free_n with (m := Ir.Config.m st) (m' := m') (l := l) (l0 := b)
                            (blk := t) (blk':= blk'); try assumption; try congruence.
    assumption. eauto.
  }
  { (*( Ir.Memory.get (Ir.Config.m st) b = None *)
    assert (H0:Ir.Memory.get m' b = None).
    { eapply Ir.Memory.get_free_none. apply wf_m.
      eassumption. eassumption. }
    rewrite H0. reflexivity.
  }
Qed.

(* Lemma: Ir.SmallStep.icmp_eq_ptr returns unchanged value even
   if Memory.free is called *)
Lemma icmp_ule_ptr_free_invariant:
  forall md st op1 op2 p1 p2 m' l
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.icmp_ule_ptr p1 p2 m' =
    Ir.SmallStep.icmp_ule_ptr p1 p2 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr.
  destruct p1.
  { destruct p2.
    { destruct (b =? b0) eqn:HBB0.
      {
        erewrite icmp_ule_ptr_nondet_cond_free_invariant.
        destruct (Ir.Memory.get (Ir.Config.m st) b) eqn:Hgetb.
        { dup Hgetb. apply Ir.Memory.get_free_some with (m' := m') (l0 := l) in Hgetb0.
          destruct Hgetb0 as [blk' Hgetb'].
          rewrite Hgetb'. reflexivity. destruct HWF.
          eassumption. eauto. }
        {
          assert (H0:Ir.Memory.get m' b = None).
          { eapply Ir.Memory.get_free_none.
            destruct HWF.
            eassumption. eassumption.
            assumption. }
          rewrite H0. reflexivity.
        }
        eassumption.
        eassumption.
        eassumption.
        eassumption.
      }
      { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond. rewrite HBB0. reflexivity. }
    }
    { erewrite p2N_free_invariant. reflexivity.
      eassumption. eassumption. eassumption. }
  }
  { destruct p2.
    { erewrite p2N_free_invariant. reflexivity.
      eassumption. eassumption. eassumption. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
Qed.

Theorem reorder_free_icmp_ule:
  forall i1 i2 r2 (opptr1 op21 op22:Ir.op) opty2
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.iicmp_ule r2 opty2 op21 op22),
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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    {
      rewrite incrpc_update_m in HNEXT.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite Ir.Config.cur_inst_update_m in HNEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite HLOCATE2 in HNEXT.
      repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
      repeat (rewrite get_val_incrpc in HNEXT).
      des_ifs; try(
                   eexists; split;
                   [ eapply Ir.SmallStep.ns_success;
                     [ eapply Ir.SmallStep.ns_one;
                       eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite HLOCATE1';
                       rewrite Heq1; try rewrite Heq2; reflexivity
                     | eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite cur_inst_update_reg_and_incrpc;
                       apply incrpc'_incrpc in HLOCATE_NEXT';
                       rewrite HLOCATE_NEXT' in HLOCATE2';
                       rewrite HLOCATE2';
                       get_val_independent_goal opptr1 r2;
                       rewrite Heq;
                       rewrite m_update_reg_and_incrpc;
                       rewrite Heq0;
                       reflexivity ]
                   | rewrite nstep_eq_trans_3;
                     apply nstep_eq_refl
                   ]
                 ).
      { eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            rewrite Heq1. rewrite Heq2.
            rewrite m_update_m in Heq3.
            assert (HPTR:Ir.SmallStep.icmp_ule_ptr p0 p1 (Ir.Config.m st) =
                         Ir.SmallStep.icmp_ule_ptr p0 p1 t).
            { unfold Ir.SmallStep.free in Heq0.
              des_ifs; erewrite <- icmp_ule_ptr_free_invariant; try eauto.
            }
            rewrite HPTR, Heq3. reflexivity.
          }
          { eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq.
            rewrite m_update_reg_and_incrpc.
            rewrite Heq0.
            reflexivity.
          }
        }
        { rewrite nstep_eq_trans_3;
            apply nstep_eq_refl.
        }
      }
    }
    { (* icmp nondet *)
      apply incrpc'_incrpc in HLOCATE_NEXT.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite cur_inst_incrpc_update_m in HCUR.
      rewrite HLOCATE2 in HCUR.
      inv HCUR.
      rewrite get_val_incrpc in HOP1.
      rewrite get_val_incrpc in HOP2.
      rewrite Ir.Config.get_val_update_m in HOP1.
      rewrite Ir.Config.get_val_update_m in HOP2.
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        { eapply Ir.SmallStep.ns_one.
          eapply Ir.SmallStep.s_icmp_ule_nondet; try reflexivity.
          rewrite HLOCATE1'. reflexivity. eassumption. eassumption.
          rewrite incrpc_update_m in HNONDET.
          rewrite m_update_m in HNONDET.
          assert (HPTR:Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st) =
                       Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 t).
          { unfold Ir.SmallStep.free in Heq0.
            des_ifs; erewrite <- icmp_ule_ptr_nondet_cond_free_invariant; eauto. }
          rewrite HPTR. assumption.
        }
        { eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite cur_inst_update_reg_and_incrpc.
          apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite HLOCATE2'.
          get_val_independent_goal opptr1 r2.
          rewrite Heq.
          rewrite m_update_reg_and_incrpc.
          rewrite Heq0.
          reflexivity.
        }
      }
      { rewrite incrpc_update_m.
        rewrite nstep_eq_trans_3.
        eapply nstep_eq_refl.
      }
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
      des_ifs.
      {
        assert (HSUCC := icmp_ule_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_ule_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. rewrite m_update_reg_and_incrpc.
            rewrite Heq0. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_ule_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := icmp_ule_always_succeeds st md' r2 opty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of icmp_ule - free:

   r1 = iicmp_ule opty1 op11 op12
   free opptr2
   ->
   free opptr2
   r1 = iicmp_ule opty1 op11 op12
**********************************************)

Theorem reorder_icmp_ule_free:
  forall i1 i2 r1 (op11 op12 opptr2:Ir.op) opty1
         (HINST1:i1 = Ir.Inst.iicmp_ule r1 opty1 op11 op12)
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
    { (* icmp det *)
      unfold_det HNEXT HLOCATE1.
      des_ifs;
        inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                          rewrite HLOCATE2 in HCUR; congruence);
        try (
            (* icmp int , int / int , poison / .. *)
            (* free deterministic. *)
            unfold_det HNEXT HLOCATE2;
            get_val_independent_H HNEXT opptr2 r1;
            rewrite m_update_reg_and_incrpc in HNEXT;
            des_ifs; try
                       ( (* free went wrong. *)
                         eexists; split;
                         [ eapply Ir.SmallStep.ns_goes_wrong;
                           eapply Ir.SmallStep.ns_one;
                           eapply Ir.SmallStep.s_det;
                           unfold Ir.SmallStep.inst_det_step;
                           rewrite HLOCATE1';
                           try rewrite Heq0; try rewrite Heq1;
                           try rewrite Heq2; try rewrite Heq3; reflexivity
                         | constructor; reflexivity ]
                       );
            ( (* free succeed. *)
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ eapply Ir.SmallStep.ns_one;
                  eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite HLOCATE1';
                  try rewrite Heq0; try rewrite Heq1;
                  try rewrite Heq2; try rewrite Heq3; reflexivity
                | eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_incrpc_update_m;
                  rewrite HLOCATE2';
                  repeat (rewrite get_val_incrpc);
                  repeat (rewrite Ir.Config.get_val_update_m);
                  rewrite Heq; try rewrite Heq0; reflexivity
                ]
              | rewrite <- nstep_eq_trans_3;
                rewrite incrpc_update_m;
                apply nstep_eq_refl
              ]
            )
          ).
      { (* icmp_eq_ptr succeeds *)
        unfold_det HNEXT HLOCATE2.
        get_val_independent_H HNEXT opptr2 r1.
        rewrite m_update_reg_and_incrpc in HNEXT.
        des_ifs;
          try ( (* free went wrong. *)
              eexists; split;
              [ eapply Ir.SmallStep.ns_goes_wrong;
                eapply Ir.SmallStep.ns_one;
                eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                rewrite HLOCATE1';
                try rewrite Heq1; try rewrite Heq2; try rewrite Heq3; reflexivity
              | constructor; reflexivity ]
            ).
        { (* free succeed. *)
          eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite HLOCATE1'.
              try rewrite Heq1; try rewrite Heq2; rewrite Heq3. reflexivity.
            }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'.
              repeat (rewrite get_val_incrpc).
              repeat (rewrite Ir.Config.get_val_update_m).
              rewrite Heq, Heq0.
              rewrite incrpc_update_m.
              rewrite m_update_m.
              assert (HPTR:Ir.SmallStep.icmp_ule_ptr p p0 t =
                           Ir.SmallStep.icmp_ule_ptr p p0 (Ir.Config.m st)).
              { unfold Ir.SmallStep.free in Heq3.
                des_ifs; erewrite <- icmp_ule_ptr_free_invariant; eauto. }
              rewrite HPTR. rewrite Heq1.
              reflexivity.
            }
          }
          { rewrite <- nstep_eq_trans_3.
            apply nstep_eq_refl.
          }
        }
      }
    }
    { (* icmp nondet *)
      inv HSINGLE; try (
        rewrite cur_inst_update_reg_and_incrpc in HCUR0;
        rewrite HLOCATE2 in HCUR0; congruence).
      (* getting free cases by destruct.. *)
      unfold_det HNEXT HLOCATE2.
      get_val_independent_H HNEXT opptr2 r.
      rewrite m_update_reg_and_incrpc in HNEXT.
      rewrite HLOCATE1 in HCUR. inv HCUR.
      symmetry in HNEXT.
      des_ifs; try
      ( (* free went wrong. *)
        eexists; split;
        [ eapply Ir.SmallStep.ns_goes_wrong;
            eapply Ir.SmallStep.ns_one;
            eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite HLOCATE1'; rewrite Heq; try rewrite Heq0; reflexivity 
        | constructor; reflexivity ]).
      { (* free succeed. *)
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            rewrite Heq. rewrite Heq0. reflexivity.
          }
          { eapply Ir.SmallStep.s_icmp_ule_nondet.
            { rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'. reflexivity. }
            { reflexivity. }
            { rewrite get_val_incrpc_update_m.
              eassumption. }
            { rewrite get_val_incrpc_update_m.
              eassumption. }
            { rewrite m_incrpc_update_m.
              assert (HNONDETCND:
                        Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 t =
                        Ir.SmallStep.icmp_ule_ptr_nondet_cond p1 p2 (Ir.Config.m st)).
              { unfold Ir.SmallStep.free in Heq0.
                des_ifs; erewrite icmp_ule_ptr_nondet_cond_free_invariant; eauto. }
              rewrite HNONDETCND.
              eassumption. }
          }
        }
        { rewrite <- nstep_eq_trans_3.
          rewrite incrpc_update_m.
          apply nstep_eq_refl.
        }
      }
    }
  - (* icmp never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.iicmp_ule r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* inttoptr never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.iicmp_ule r1 opty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of malloc - psub:

   r1 = malloc ty opptr1
   r2 = psub opty2 op21 op22
   ->
   r2 = psub opty2 op21 op22
   r1 = malloc ty opptr1.
**********************************************)

Lemma psub_always_succeeds:
  forall st (md:Ir.IRModule.t) r retty ptrty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r retty ptrty op1 op2)),
  exists st' v,
    (Ir.SmallStep.inst_step md st (Ir.SmallStep.sr_success Ir.e_none st') /\
    (st' = Ir.SmallStep.update_reg_and_incrpc md st r v)).
Proof.
  intros.
  destruct (Ir.Config.get_val st op1) eqn:Hop1;
      destruct (Ir.Config.get_val st op2) eqn:Hop2;
      (eexists; eexists; split;
       [ eapply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
         rewrite HCUR; rewrite Hop1; reflexivity
       | reflexivity ]).
Qed.

Lemma psub_always_succeeds2:
  forall st st' (md:Ir.IRModule.t) r retty ptrty op1 op2
         (HCUR: Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r retty ptrty op1 op2))
         (HSTEP: Ir.SmallStep.inst_step md st st'),
  exists v, st' = Ir.SmallStep.sr_success Ir.e_none
                                (Ir.SmallStep.update_reg_and_incrpc md st r v).
Proof.
  intros.
  inv HSTEP; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  destruct (Ir.Config.get_val st op1) eqn:Hop1;
    destruct (Ir.Config.get_val st op2) eqn:Hop2;
    try (des_ifs; eexists; reflexivity).
Qed.

Lemma psub_new_invariant:
  forall md l m' (p1 p2:Ir.ptrval) st nsz contents P op1 op2 (sz:nat)
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HALLOC:Ir.Memory.allocatable (Ir.Config.m st) (map (fun addr : nat => (addr, nsz)) P) = true)
         (HSZ:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) contents P))
         (HNEW:(m', l) =
               Ir.Memory.new (Ir.Config.m st) Ir.heap nsz Ir.SYSALIGN contents P),
    Ir.SmallStep.psub p1 p2 (Ir.Config.m (Ir.Config.update_m st m')) sz =
    Ir.SmallStep.psub p1 p2 (Ir.Config.m st) sz.
Proof.
  intros.
  unfold Ir.SmallStep.psub.
  destruct p1.
  { destruct p2; try reflexivity.
    erewrite p2N_new_invariant; try eassumption. reflexivity.
  }
  { destruct p2.
    { erewrite p2N_new_invariant;try eassumption. reflexivity. }
    reflexivity.
  }
Qed.

Theorem reorder_malloc_psub:
  forall i1 i2 r1 r2 (opptr1 op21 op22:Ir.op) ty1 retty2 ptrty2
         (HINST1:i1 = Ir.Inst.imalloc r1 ty1 opptr1)
         (HINST2:i2 = Ir.Inst.ipsub r2 retty2 ptrty2 op21 op22),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* malloc succeeds. *)
    inv HSUCC; try (inv HSUCC0; fail).
    exploit inst_step_incrpc. eapply HLOCATE_NEXT. eapply HSINGLE0.
    intros HCUR'.
    inv HSINGLE; try congruence.
    (* psub works deterministically. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite <- HCUR' in HNEXT.
    rewrite HLOCATE2 in HNEXT.
    apply incrpc'_incrpc in HLOCATE_NEXT'.
    rewrite HLOCATE_NEXT' in HLOCATE2'.
    (* now get malloc's behavior *)
    inv HSINGLE0; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT0. rewrite HLOCATE1 in HNEXT0.
      congruence.
    + (* Malloc returned NULL. *)
      inv_cur_inst HCUR HLOCATE1.
      get_val_independent_H HNEXT op21 r1.
      get_val_independent_H HNEXT op22 r1.
      rewrite m_update_reg_and_incrpc in HNEXT.
      destruct (Ir.Config.get_val st op21) eqn:Hop21;
        destruct (Ir.Config.get_val st op22) eqn:Hop22.
      { destruct v; destruct v0; try inv HNEXT;
        try (eexists; split;
        [ eapply Ir.SmallStep.ns_success;
          [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22
          | s_malloc_null_trivial HLOCATE2';
            get_val_independent_goal opptr1 r2]
         | eapply nstep_eq_trans_1;
          [ assert (r1 <> r2) by admit; assumption | apply nstep_eq_refl ] ]).
      }
      { destruct v; try inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
      }
      { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
      }
      { inv HNEXT; try (
          eexists; split;
          [ eapply Ir.SmallStep.ns_success; [ eapply Ir.SmallStep.ns_one;
            inst_step_det_trivial HLOCATE1' Hop21 Hop22 |
            s_malloc_null_trivial HLOCATE2'; get_val_independent_goal opptr1 r2 ]
          | eapply nstep_eq_trans_1; [ assert (r1 <> r2) by admit;
            assumption | apply nstep_eq_refl] ]).
      }
    + (* malloc succeeded. *)
      get_val_independent_H HNEXT op21 r.
      get_val_independent_H HNEXT op22 r.
      inv_cur_inst HCUR HLOCATE1.
      repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
      rewrite m_update_reg_and_incrpc in HNEXT.
      des_ifs; try (
        eexists; split;
        [ eapply Ir.SmallStep.ns_success;
          [ apply Ir.SmallStep.ns_one;
            try (inst_step_det_trivial HLOCATE1' Heq Heq0; fail);
            try (apply Ir.SmallStep.s_det; unfold Ir.SmallStep.inst_det_step;
                 rewrite HLOCATE1'; reflexivity)
          | s_malloc_trivial HLOCATE2'; get_val_independent_goal opptr1 r2
          ]
        | eapply nstep_eq_trans_2;
          [ assert (r2 <> r1) by admit; congruence
          | apply nstep_eq_refl
          ]
        ]).
      { eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - apply Ir.SmallStep.ns_one.
            apply Ir.SmallStep.s_det. unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'. rewrite Heq. rewrite Heq0.
            reflexivity.
          - s_malloc_trivial HLOCATE2'. get_val_independent_goal opptr1 r2.
        }
        { eapply nstep_eq_trans_2.
          { assert (r2 <> r1) by admit; congruence. }
          { assert (HPSUB:Ir.SmallStep.psub p p0 m' n =
                          Ir.SmallStep.psub p p0 (Ir.Config.m st) n).
            { erewrite <- psub_new_invariant; eauto. rewrite m_update_m.
              reflexivity. }
            rewrite HPSUB. apply nstep_eq_refl. }
        }
      }
  - (* malloc raised oom. *)
    inv HOOM.
    + inv HSINGLE. unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HLOCATE1 in HNEXT. inv HNEXT.
      inv_cur_inst HCUR HLOCATE1.
      (* psub only succeeds. *)
      assert (HSUCC := psub_always_succeeds st md' r2 retty2 ptrty2
                                                   op21 op22 HLOCATE1').
      destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
      eexists. split.
      { eapply Ir.SmallStep.ns_success.
        - eapply Ir.SmallStep.ns_one.
          eapply HSUCC1.
        - eapply Ir.SmallStep.s_malloc_oom.
          rewrite HSUCC2. apply incrpc'_incrpc in HLOCATE_NEXT'.
          rewrite HLOCATE_NEXT' in HLOCATE2'.
          rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
          reflexivity.
          reflexivity.
          rewrite HSUCC2. get_val_independent_goal opptr1 r2.
          rewrite HSUCC2. rewrite m_update_reg_and_incrpc. eassumption.
      }
      { constructor. reflexivity. }
    + inv HSUCC.
    + inv HOOM0.
  - (* malloc never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw (Ir.Inst.imalloc r1 ty1 opptr1)).
      reflexivity. eapply HLOCATE1. eassumption.
      intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of psub - malloc:

   r1 = psub retty1 ptrty1 op11 op12
   r2 = malloc ty2 opptr2
   ->
   r2 = malloc ty2 opptr2
   r1 = psub retty1 ptrty1 op11 op12
**********************************************)

Theorem reorder_psub_malloc:
  forall i1 i2 r1 r2 (op11 op12 opptr2:Ir.op) retty1 ptrty1 ty2
         (HINST1:i1 = Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)
         (HINST2:i2 = Ir.Inst.imalloc r2 ty2 opptr2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  unfold inst_reordering_valid.
  intros.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - (* psub - always succeed. :) *)
    inv HSUCC; try (inv HSUCC0; fail).
    assert (HCUR':Ir.Config.cur_inst md c' = Ir.Config.cur_inst md st_next).
      { symmetry. eapply inst_step_incrpc. eassumption.
        eassumption. }
    inv HSINGLE; try congruence.
    + unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite HCUR' in HNEXT. rewrite HLOCATE2 in HNEXT. inv HNEXT.
    + (* malloc returns null *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      {
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT. inv HNEXT.
        des_ifs;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ eapply Ir.SmallStep.ns_one;
                  s_malloc_null_trivial HLOCATE1';
                  get_val_independent_H HZERO opptr2 r1
                | eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite HLOCATE2';
                  try (get_val_independent_goal op11 r2;
                  rewrite Heq);
                  try (get_val_independent_goal op12 r2;
                       rewrite Heq0);
                  reflexivity ]
              | rewrite nstep_eq_trans_1;
                [ apply nstep_eq_refl | assert (r1 <> r2) by admit; congruence ] ]).
        { eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_null_trivial HLOCATE1'.
            }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Heq.
              get_val_independent_goal op12 r2.
              rewrite Heq0.
              rewrite m_update_reg_and_incrpc.
              reflexivity.
            }
          }
          { rewrite nstep_eq_trans_1. apply nstep_eq_refl.
            assert (r1 <> r2). admit. congruence. }
        }
      }
    + (* oom *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply psub_always_succeeds2 with (r := r1) (retty := retty1)
                                       (ptrty := ptrty1)
                                       (op1 := op11) (op2 := op12) in HSINGLE0.
      destruct HSINGLE0 as [vtmp HSINGLE0]. inv HSINGLE0.
      eexists (nil, Ir.SmallStep.sr_oom).
      split.
      { eapply Ir.SmallStep.ns_oom.
        eapply Ir.SmallStep.ns_one.
        eapply Ir.SmallStep.s_malloc_oom.
        rewrite HLOCATE1'. reflexivity. reflexivity.
        get_val_independent_H HSZ opptr2 r1. eassumption.
        rewrite m_update_reg_and_incrpc in HNOSPACE.
        assumption.
      }
      { constructor. reflexivity. }
      assumption.
    + (* malloc succeeds *)
      rewrite HCUR' in HCUR. rewrite HLOCATE2 in HCUR. inv HCUR.
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      inv HSINGLE0; try congruence.
      { (* psub is determinsitic *)
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite HLOCATE1 in HNEXT.
        des_ifs;
          rewrite m_update_reg_and_incrpc in *;
          rewrite cur_inst_update_reg_and_incrpc in *;
          try (
              eexists; split;
              [ eapply Ir.SmallStep.ns_success;
                [ (* malloc *)
                  eapply Ir.SmallStep.ns_one;
                  eapply Ir.SmallStep.s_malloc; try (eauto; fail);
                  try eassumption;
                  try get_val_independent_H HSZ opptr2 r1
                | (* psub, det *)
                  eapply Ir.SmallStep.s_det;
                  unfold Ir.SmallStep.inst_det_step;
                  rewrite cur_inst_update_reg_and_incrpc;
                  rewrite cur_inst_incrpc_update_m;
                  rewrite HLOCATE2';
                  try (get_val_independent_goal op11 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq);
                  try (get_val_independent_goal op12 r2;
                  rewrite Ir.Config.get_val_update_m;
                  rewrite Heq0);
                  reflexivity
                ]
              | eapply nstep_eq_trans_2;
                [ assert (r1 <> r2) by admit; assumption
                | apply nstep_eq_refl ]
              ]).
        { (* psub deterministic *)
          eexists. split.
          { eapply Ir.SmallStep.ns_success.
            { eapply Ir.SmallStep.ns_one.
              s_malloc_trivial HLOCATE1'.
              get_val_independent_H HSZ opptr2 r1. }
            { eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step.
              rewrite cur_inst_update_reg_and_incrpc.
              rewrite cur_inst_incrpc_update_m.
              rewrite HLOCATE2'.
              get_val_independent_goal op11 r2.
              rewrite Ir.Config.get_val_update_m, Heq.
              get_val_independent_goal op12 r2.
              rewrite Ir.Config.get_val_update_m, Heq0.
              rewrite m_update_reg_and_incrpc.
              rewrite m_update_m.
              assert (HPTR:Ir.SmallStep.psub p p0 m' n =
                           Ir.SmallStep.psub p p0 (Ir.Config.m st) n).
              { erewrite <- psub_new_invariant; eauto. rewrite m_update_m. reflexivity. }
              rewrite HPTR. reflexivity.
            }
          }
          {
            rewrite nstep_eq_trans_2.
            { apply nstep_eq_refl. }
            { assert (r1 <> r2) by admit. congruence. }
          }
        }
      }
  - (* psub never raises OOM. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* psub never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw
                          (Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of free - psub:

   free opptr1
   r2 = psub retty2 ptrty2 op21 op22
   ->
   r2 = psub retty2 ptrty2 op21 op22
   free opptr1
**********************************************)

(* Lemma: Ir.SmallStep.psub returns unchanged value even
   if Memory.free is called *)
Lemma psub_free_invariant:
  forall md st op1 op2 p1 p2 m' l sz
         (HWF:Ir.Config.wf md st)
         (HGV1: Ir.Config.get_val st op1 = Some (Ir.ptr p1))
         (HGV2: Ir.Config.get_val st op2 = Some (Ir.ptr p2))
         (HFREE:Some m' = Ir.Memory.free (Ir.Config.m st) l),
    Ir.SmallStep.psub p1 p2 m' sz =
    Ir.SmallStep.psub p1 p2 (Ir.Config.m st) sz.
Proof.
  intros.
  unfold Ir.SmallStep.psub.
  destruct p1.
  { destruct p2; try reflexivity.
    { erewrite p2N_free_invariant; eauto. }
  }
  { destruct p2.
    { erewrite p2N_free_invariant; eauto. }
    { unfold Ir.SmallStep.p2N. reflexivity. }
  }
Qed.

Theorem reorder_free_psub:
  forall i1 i2 r2 (opptr1 op21 op22:Ir.op) retty2 ptrty2
         (HINST1:i1 = Ir.Inst.ifree opptr1)
         (HINST2:i2 = Ir.Inst.ipsub r2 retty2 ptrty2 op21 op22),
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
      (rewrite incrpc_update_m in HCUR; rewrite Ir.Config.cur_inst_update_m in HCUR;
       apply incrpc'_incrpc in HLOCATE_NEXT; rewrite HLOCATE_NEXT in HLOCATE2;
       congruence; fail).
    {
      rewrite incrpc_update_m in HNEXT.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite Ir.Config.cur_inst_update_m in HNEXT.
      apply incrpc'_incrpc in HLOCATE_NEXT.
      rewrite HLOCATE_NEXT in HLOCATE2.
      rewrite HLOCATE2 in HNEXT.
      repeat (rewrite Ir.Config.get_val_update_m in HNEXT).
      repeat (rewrite get_val_incrpc in HNEXT).
      des_ifs; try(
                   eexists; split;
                   [ eapply Ir.SmallStep.ns_success;
                     [ eapply Ir.SmallStep.ns_one;
                       eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite HLOCATE1';
                       try rewrite Heq1; try rewrite Heq2; reflexivity
                     | eapply Ir.SmallStep.s_det;
                       unfold Ir.SmallStep.inst_det_step;
                       rewrite cur_inst_update_reg_and_incrpc;
                       apply incrpc'_incrpc in HLOCATE_NEXT';
                       rewrite HLOCATE_NEXT' in HLOCATE2';
                       rewrite HLOCATE2';
                       get_val_independent_goal opptr1 r2;
                       rewrite Heq;
                       rewrite m_update_reg_and_incrpc;
                       rewrite Heq0;
                       reflexivity ]
                   | rewrite nstep_eq_trans_3;
                     apply nstep_eq_refl
                   ]
                 ).
      { eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            rewrite Heq1. rewrite Heq2.
            assert (HPTR:Ir.SmallStep.psub p0 p1 (Ir.Config.m st) n =
                         Ir.SmallStep.psub p0 p1 t n).
            { unfold Ir.SmallStep.free in Heq0.
              des_ifs; erewrite <- psub_free_invariant; eauto. }
            rewrite HPTR. reflexivity.
          }
          { eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq.
            rewrite m_update_reg_and_incrpc.
            rewrite Heq0.
            reflexivity.
          }
        }
        { rewrite nstep_eq_trans_3;
            apply nstep_eq_refl.
        }
      }
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
      apply incrpc'_incrpc in HLOCATE_NEXT'.
      rewrite HLOCATE_NEXT' in HLOCATE2'.
      des_ifs.
      {
        assert (HSUCC := psub_always_succeeds st md' r2 retty2 ptrty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2. 
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := psub_always_succeeds st md' r2 retty2 ptrty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. rewrite m_update_reg_and_incrpc.
            rewrite Heq0. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := psub_always_succeeds st md' r2 retty2 ptrty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
      {
        assert (HSUCC := psub_always_succeeds st md' r2 retty2 ptrty2
                                                 op21 op22 HLOCATE1').
        destruct HSUCC as [st'tmp [v'tmp [HSUCC1 HSUCC2]]].
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          - eapply Ir.SmallStep.ns_one.
            eapply HSUCC1.
          - eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HSUCC2.
            rewrite cur_inst_update_reg_and_incrpc. rewrite HLOCATE2'.
            get_val_independent_goal opptr1 r2.
            rewrite Heq. reflexivity.
        }
        { constructor. reflexivity. }
      }
    + inv HSUCC.
    + inv HGW0.
Admitted.



(********************************************
   REORDERING of psub - free:

   r1 = psub retty1 ptrty1 op11 op12
   free opptr2
   ->
   free opptr2
   r1 = psub retty1 ptrty1 op11 op12
**********************************************)

Theorem reorder_psub_free:
  forall i1 i2 r1 (op11 op12 opptr2:Ir.op) retty1 ptrty1
         (HINST1:i1 = Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)
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
    (* psub det *)
    unfold_det HNEXT HLOCATE1.
    des_ifs;
      inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in HCUR;
                        rewrite HLOCATE2 in HCUR; congruence);
      try (
          (* psub int , int / int , poison / .. *)
          (* free deterministic. *)
          unfold_det HNEXT HLOCATE2;
          get_val_independent_H HNEXT opptr2 r1;
          rewrite m_update_reg_and_incrpc in HNEXT;
          des_ifs; try
                     ( (* free went wrong. *)
                       eexists; split;
                       [ eapply Ir.SmallStep.ns_goes_wrong;
                         eapply Ir.SmallStep.ns_one;
                         eapply Ir.SmallStep.s_det;
                         unfold Ir.SmallStep.inst_det_step;
                         rewrite HLOCATE1';
                         try rewrite Heq;
                         try rewrite Heq0; try rewrite Heq1;
                         try rewrite Heq2; try rewrite Heq3; reflexivity
                       | constructor; reflexivity ]
                     );
          ( (* free succeed. *)
            eexists; split;
            [ eapply Ir.SmallStep.ns_success;
              [ eapply Ir.SmallStep.ns_one;
                eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                rewrite HLOCATE1';
                try rewrite Heq;
                try rewrite Heq0; try rewrite Heq1;
                try rewrite Heq2; try rewrite Heq3; reflexivity
              | eapply Ir.SmallStep.s_det;
                unfold Ir.SmallStep.inst_det_step;
                rewrite cur_inst_incrpc_update_m;
                rewrite HLOCATE2';
                repeat (rewrite get_val_incrpc);
                repeat (rewrite Ir.Config.get_val_update_m);
                try rewrite Heq; try rewrite Heq0; reflexivity
              ]
            | rewrite <- nstep_eq_trans_3;
              rewrite incrpc_update_m;
              apply nstep_eq_refl
            ]
          )
        ).
    { (* psub succeeds *)
      unfold_det HNEXT HLOCATE2.
      get_val_independent_H HNEXT opptr2 r1.
      rewrite m_update_reg_and_incrpc in HNEXT.
      des_ifs;
        try ( (* free went wrong. *)
            eexists; split;
            [ eapply Ir.SmallStep.ns_goes_wrong;
              eapply Ir.SmallStep.ns_one;
              eapply Ir.SmallStep.s_det;
              unfold Ir.SmallStep.inst_det_step;
              rewrite HLOCATE1';
              try rewrite Heq1; try rewrite Heq2; try rewrite Heq3; reflexivity
            | constructor; reflexivity ]
          ).
      { (* free succeed. *)
        eexists. split.
        { eapply Ir.SmallStep.ns_success.
          { eapply Ir.SmallStep.ns_one.
            eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            try rewrite Heq1; try rewrite Heq2; reflexivity.
          }
          { eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_incrpc_update_m.
            rewrite HLOCATE2'.
            repeat (rewrite get_val_incrpc).
            repeat (rewrite Ir.Config.get_val_update_m).
            rewrite Heq, Heq0.
            rewrite incrpc_update_m.
            rewrite m_update_m.
            assert (HPTR:Ir.SmallStep.psub p p0 t n =
                         Ir.SmallStep.psub p p0 (Ir.Config.m st) n).
            { unfold Ir.SmallStep.free in Heq2.
              des_ifs; erewrite <- psub_free_invariant; eauto. }
            rewrite HPTR.
            reflexivity.
          }
        }
        { rewrite <- nstep_eq_trans_3.
          apply nstep_eq_refl.
        }
      }
    }
  - (* psub never rases oom. *)
    inv HOOM.
    + exfalso. exploit (no_alloc_no_oom (Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)).
      reflexivity. eapply HLOCATE1. eassumption. intros. assumption.
    + inv HSUCC.
    + inv HOOM0.
  - (* inttoptr never goes wrong. *)
    inv HGW.
    + exfalso. exploit (never_goes_wrong_no_gw
                          (Ir.Inst.ipsub r1 retty1 ptrty1 op11 op12)).
      reflexivity. eapply HLOCATE1. assumption. intros. assumption.
    + inv HSUCC.
    + inv HGW0.
Admitted.



End Reordering.

End Ir.
Require Import BinNat.
Require Import Bool.
Require Import Omega.
Require Import sflib.

Require Import Common.
Require Import Value.
Require Import Memory.
Require Import State.
Require Import Behaviors.
Require Import SmallStep.

Module Ir.

Module Refinement.

Definition refines_value (v_tgt v_src:Ir.val): bool :=
  match (v_tgt, v_src) with
  | (_, Ir.poison) => true
  | (Ir.num ntgt, Ir.num nsrc) => Nat.eqb ntgt nsrc
  | (Ir.ptr ptgt, Ir.ptr psrc) => Ir.ptr_eqb ptgt psrc
  | (_, _) => false
  end.

Definition refines_bit (b_tgt b_src:Ir.Bit.t): bool :=
  match (b_src, b_tgt) with
  | (Ir.Bit.bpoison, _) => true
  | (_, Ir.Bit.bpoison) => false
  | (Ir.Bit.bint b1, Ir.Bit.bint b2) => Bool.eqb b1 b2
  | (Ir.Bit.baddr p1 o1, Ir.Bit.baddr p2 o2) =>
    Nat.eqb o1 o2 && Ir.ptr_eqb p1 p2
  | (_, _) => false
  end.

Definition refines_byte (b_tgt b_src:Ir.Byte.t): bool :=
  refines_bit b_tgt.(Ir.Byte.b0) b_src.(Ir.Byte.b0) &&
  refines_bit b_tgt.(Ir.Byte.b1) b_src.(Ir.Byte.b1) &&
  refines_bit b_tgt.(Ir.Byte.b2) b_src.(Ir.Byte.b2) &&
  refines_bit b_tgt.(Ir.Byte.b3) b_src.(Ir.Byte.b3) &&
  refines_bit b_tgt.(Ir.Byte.b4) b_src.(Ir.Byte.b4) &&
  refines_bit b_tgt.(Ir.Byte.b5) b_src.(Ir.Byte.b5) &&
  refines_bit b_tgt.(Ir.Byte.b6) b_src.(Ir.Byte.b6) &&
  refines_bit b_tgt.(Ir.Byte.b7) b_src.(Ir.Byte.b7).

Definition refines_event (e_tgt e_src:Ir.event): bool :=
  match (e_tgt, e_src) with
  | (Ir.e_some vtgt, Ir.e_some vsrc) => Nat.eqb vtgt vsrc
  | (Ir.e_none, Ir.e_none) => true
  | _ => false
  end.

Definition refines_trace (tr_tgt tr_src:Ir.trace):bool :=
  let tr_tgt' := List.filter Ir.not_none tr_tgt in
  let tr_src' := List.filter Ir.not_none tr_src in
  if Nat.eqb (List.length tr_tgt') (List.length tr_src') then
    List.forallb (fun ee => refines_event ee.(fst) ee.(snd))
                 (List.combine tr_tgt' tr_src')
  else false.

(* If tgts_prefix is true, check whether tr_tgt has a prefix
   that refines tr_src.
   If tgts_prefix is false, check whether tr_src has a prefix
   so tr_tgt refines the prefix. *)
Definition refines_trace_prefix (tr_tgt tr_src:Ir.trace) (tgts_prefix:bool)
: bool :=
  let tr_tgt' := List.filter Ir.not_none tr_tgt in
  let tr_src' := List.filter Ir.not_none tr_src in
  let (tr_tgt', tr_src') :=
      if tgts_prefix then (List.firstn (List.length tr_src') tr_tgt', tr_src')
      else (tr_tgt', List.firstn (List.length tr_tgt') tr_src') in
  refines_trace tr_tgt' tr_src'.


(* Checks whether the behavior of a target program refines the behavior of a source program. *)
Definition refines (pb_tgt pb_src:Ir.program_behavior):bool :=
  match (pb_tgt, pb_src) with
  | (Ir.b_terminates tr_tgt ret_tgt, Ir.b_terminates tr_src ret_src) =>
    refines_trace tr_tgt tr_src && refines_value ret_tgt ret_src

  | (Ir.b_terminates tr_tgt ret_tgt, Ir.b_diverges tr_src) =>
    (* infinite loop without any event is UB.
       Chech whether target's trace has a prefix that refines trace of the source. *)
    refines_trace_prefix tr_tgt tr_src true

  | (Ir.b_terminates tr_tgt ret_tgt, Ir.b_goes_wrong tr_src) =>
    refines_trace_prefix tr_tgt tr_src true

  | (Ir.b_diverges tr_tgt, Ir.b_diverges tr_src) =>
    refines_trace tr_tgt tr_src

  | (Ir.b_diverges tr_tgt, Ir.b_goes_wrong tr_src) =>
    refines_trace tr_tgt tr_src

  | (Ir.b_goes_wrong tr_tgt, Ir.b_diverges tr_src) =>
    refines_trace tr_tgt tr_src

  | (Ir.b_goes_wrong tr_tgt, Ir.b_goes_wrong tr_src) =>
    refines_trace tr_tgt tr_src

  | (Ir.b_oom tr_tgt, Ir.b_terminates tr_src ret_src) =>
    refines_trace_prefix tr_tgt tr_src false

  | (Ir.b_oom tr_tgt, Ir.b_diverges tr_src) =>
    (* If source has UB and target has OOM,
       either the trace of source may be the prefix of the trace of target,
       or the trace of target may be the prefix of the trace of source. *)
    refines_trace_prefix tr_tgt tr_src true ||
    refines_trace_prefix tr_tgt tr_src false

  | (Ir.b_oom tr_tgt, Ir.b_goes_wrong tr_src) =>
    refines_trace_prefix tr_tgt tr_src true ||
    refines_trace_prefix tr_tgt tr_src false

  | (Ir.b_oom tr_tgt, Ir.b_oom tr_src) =>
    (* target trace should be prefix of source trace. *)
    refines_trace_prefix tr_tgt tr_src true

  | (_, _) => false
  end.

(***********************************************************
   Propositional definition of refinements on memory, state
 ***********************************************************)

Definition refines_memblock (mb_tgt mb_src:Ir.MemBlock.t) :=
  mb_tgt.(Ir.MemBlock.bt) = mb_src.(Ir.MemBlock.bt) /\
  mb_tgt.(Ir.MemBlock.r) = mb_src.(Ir.MemBlock.r) /\
  mb_tgt.(Ir.MemBlock.n) = mb_src.(Ir.MemBlock.n) /\
  mb_tgt.(Ir.MemBlock.a) = mb_src.(Ir.MemBlock.a) /\
  List.Forall2 (fun b1 b2 => refines_byte b1 b2 = true)
               mb_tgt.(Ir.MemBlock.c) mb_src.(Ir.MemBlock.c) /\
  mb_tgt.(Ir.MemBlock.P) = mb_src.(Ir.MemBlock.P).

Definition refines_memory (m_tgt m_src:Ir.Memory.t) :=
  m_tgt.(Ir.Memory.mt) = m_src.(Ir.Memory.mt) /\
  List.Forall2 (fun mbid_tgt mbid_src =>
                  fst mbid_tgt = fst mbid_src /\
                  refines_memblock (snd mbid_tgt) (snd mbid_src))
               m_tgt.(Ir.Memory.blocks) m_src.(Ir.Memory.blocks) /\
  m_tgt.(Ir.Memory.calltimes) = m_src.(Ir.Memory.calltimes) /\
  m_tgt.(Ir.Memory.fresh_bid) = m_src.(Ir.Memory.fresh_bid).

Definition refines_regfile (rf_tgt rf_src:Ir.Regfile.t) :=
  forall regid,
    (Ir.Regfile.get rf_tgt regid = None <-> Ir.Regfile.get rf_src regid = None) /\
    (forall vtgt
            (HGET:Ir.Regfile.get rf_tgt regid = Some vtgt),
        exists vsrc, Ir.Regfile.get rf_src regid = Some vsrc /\
                     refines_value vtgt vsrc = true).

Definition refines_stack (s_tgt s_src:Ir.Stack.t) :=
  List.Forall2 (fun itm_tgt itm_src =>
                  fst itm_tgt = fst itm_src /\
                  fst (snd itm_tgt) = fst (snd itm_src) /\
                  refines_regfile (snd (snd itm_tgt)) (snd (snd itm_src)))
               s_tgt s_src.

Definition refines_state (s_tgt s_src:Ir.Config.t) :=
  refines_memory s_tgt.(Ir.Config.m) s_src.(Ir.Config.m) /\
  refines_stack s_tgt.(Ir.Config.s) s_src.(Ir.Config.s) /\
  s_tgt.(Ir.Config.cid_to_f) = s_src.(Ir.Config.cid_to_f) /\
  s_tgt.(Ir.Config.cid_fresh) = s_src.(Ir.Config.cid_fresh).

Import Ir.SmallStep.

(* refines_step_res <tgt> <src> *)
Inductive refines_step_res: step_res -> step_res -> Prop :=
| srref_tgt_oom:
    forall sr_src,
      refines_step_res sr_oom sr_src
| srref_src_goes_wrong:
    forall sr_tgt,
      refines_step_res sr_tgt sr_goes_wrong
| srref_finish:
    forall v_tgt v_src
           (HREFV:refines_value v_tgt v_src),
    refines_step_res (sr_prog_finish v_tgt) (sr_prog_finish v_src)
| srref_success:
    forall e_tgt e_src s_tgt s_src
           (HREFE:refines_event e_tgt e_src)
           (HREFS:refines_state s_tgt s_src), (* Just checks equality. *)
    refines_step_res (sr_success e_tgt s_tgt) (sr_success e_src s_src).



(***********************************************************
               Lemmas about refinement.
 ***********************************************************)

Theorem refines_value_refl:
  forall (v:Ir.val), refines_value v v = true.
Proof.
  intros.
  destruct v; unfold refines_value.
  - rewrite Nat.eqb_eq. auto.
  - rewrite Ir.ptr_eqb_refl. reflexivity.
  - reflexivity.
Qed.

Theorem refines_value_trans:
  forall (v1 v2 v3:Ir.val)
         (HREF1:refines_value v1 v2 = true)
         (HREF2:refines_value v2 v3 = true),
    refines_value v1 v3 = true.
Proof.
  intros.
  unfold refines_value in *.
  des_ifs.
  rewrite PeanoNat.Nat.eqb_eq in *.
  congruence.
  unfold Ir.ptr_eqb in *.
  des_ifs; try rewrite andb_true_iff in *;
    repeat (rewrite PeanoNat.Nat.eqb_eq in *);
    destruct HREF1; destruct HREF2;
    try congruence.
  split; congruence.
  repeat (rewrite andb_true_iff in *);
    repeat (rewrite PeanoNat.Nat.eqb_eq in *).
  destruct H. destruct H. destruct H1.  destruct H1.
  split; try congruence.
  split; try congruence.
  split; try congruence.
  eapply list_inclb_trans. eapply H4. ss.
  eapply list_inclb_trans. eapply H5. ss.
  split; try ss.
  repeat (rewrite andb_true_iff in *).
  repeat (rewrite PeanoNat.Nat.eqb_eq in *).
  intuition.
  eapply list_inclb_trans. eapply H6. ss.
  eapply list_inclb_trans. eapply H5. ss.
Qed.

Theorem refines_bit_refl:
  forall b, refines_bit b b = true.
Proof.
  unfold refines_bit.
  intros.
  destruct b. destruct b; reflexivity.
  unfold Ir.ptr_eqb.
  destruct p; repeat (rewrite PeanoNat.Nat.eqb_refl); try reflexivity.
  repeat (rewrite Common.list_inclb_refl).
  destruct o. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma ptr_eqb_trans:
  forall p1 p2 p3
         (H1:Ir.ptr_eqb p1 p2 = true)
         (H2:Ir.ptr_eqb p2 p3 = true),
    Ir.ptr_eqb p1 p3 = true.
Proof.
  intros.
  unfold Ir.ptr_eqb in *.
  des_ifs; repeat (rewrite andb_true_iff in *);
           repeat (rewrite PeanoNat.Nat.eqb_eq in *);
           try (inv H1; inv H0; fail);
           try (inv H2; inv H0; fail).
  intuition.
  { inv H1. inv H. inv H0.
    inv H2. inv H. inv H0. 
    split; try ss.
    split. { split. congruence.
             eapply list_inclb_trans. eapply H3. ss. }
           { eapply list_inclb_trans. eapply H2. ss. }
  }
  { inv H1. inv H. inv H1.
    inv H2. inv H. inv H2. 
    split; try ss.
    split. { split. congruence.
             eapply list_inclb_trans. eapply H4. ss. }
           { eapply list_inclb_trans. eapply H5. ss. }
  }
Qed.

Theorem refines_bit_trans:
  forall b1 b2 b3
         (HREF1:refines_bit b1 b2 = true)
         (HREF2:refines_bit b2 b3 = true),
    refines_bit b1 b3 = true.
Proof.
  intros.
  unfold refines_bit in *.
  des_ifs.
  unfold eqb in *. des_ifs.
  rewrite andb_true_iff in *.
  repeat (rewrite PeanoNat.Nat.eqb_eq in *).
  intuition.
  eapply ptr_eqb_trans. eassumption. ss.
Qed.

Ltac unfold_all_ands_H :=
  repeat (match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end).

Theorem refines_byte_trans:
  forall b1 b2 b3
         (HREF1:refines_byte b1 b2 = true)
         (HREF2:refines_byte b2 b3 = true),
    refines_byte b1 b3 = true.
Proof.
  intros.
  unfold refines_byte in *.
  repeat (rewrite andb_true_iff in *).
  unfold_all_ands_H.
  repeat (split; try (eapply refines_bit_trans; try eassumption; assumption)).
Qed.

Theorem refines_memblock_refl:
  forall mb1,
    refines_memblock mb1 mb1.
Proof.
  intros.
  repeat (split;try congruence).
  apply Forall2_samelist.
  intros.
  unfold refines_byte.
  repeat (rewrite andb_true_iff).
  repeat (rewrite refines_bit_refl).
  repeat (split; try reflexivity).
Qed.

Theorem refines_memblock_trans:
  forall mb1 mb2 mb3
         (HREF1:refines_memblock mb1 mb2)
         (HREF1:refines_memblock mb2 mb3),
    refines_memblock mb1 mb3.
Proof.
  intros.
  inv HREF1. inv H0. inv H2. inv H3.
  inv HREF0. inv H5. inv H7. inv H8.
  inv H4. inv H9.
  repeat (split;try congruence).
  eapply Forall2_trans.
  { intros. eapply refines_byte_trans. eassumption. ss.
  }
  eassumption. assumption.
Qed.

Theorem refines_memory_refl:
  forall (m1:Ir.Memory.t),
    refines_memory m1 m1.
Proof.
  intros.
  split.
  { congruence. }
  split.
  { eapply Forall2_samelist.
    intros. split. reflexivity. apply refines_memblock_refl.
  }
  split; reflexivity.
Qed.
    
Theorem refines_memory_trans:
  forall m1 m2 m3
         (HREF1:refines_memory m1 m2)
         (HREF1:refines_memory m2 m3),
    refines_memory m1 m3.
Proof.
  intros.
  destruct HREF1.
  destruct HREF0.
  unfold_all_ands_H.
  repeat (split; try congruence).
  eapply Forall2_trans.
  { intros.
    unfold_all_ands_H.
    split. congruence. eapply refines_memblock_trans. eassumption. ss.
  }
  eassumption. assumption.
Qed.

Theorem refines_event_refl:
  forall (e:Ir.event), refines_event e e = true.
Proof.
  intros.
  destruct e. unfold refines_event. reflexivity.
  unfold refines_event. rewrite Nat.eqb_eq. reflexivity.
Qed.

Theorem refines_trace_refl:
  forall (t:Ir.trace), refines_trace t t = true.
Proof.
  intros.
  induction t.
  - reflexivity.
  - unfold refines_trace in *.
    assert (forall {X:Type} (l:list X), (List.length l =? List.length l) = true).
    { intros.
      rewrite Nat.eqb_eq. reflexivity. }
    rewrite H. rewrite H in IHt.
    simpl.
    destruct (Ir.not_none a) eqn:HNN.
    simpl. rewrite IHt. rewrite refines_event_refl. reflexivity.
    assumption.
Qed.

Theorem refines_trace_prefix_refl:
  forall (t:Ir.trace) b, refines_trace_prefix t t b = true.
Proof.
  intros.
  destruct b; unfold refines_trace_prefix in *;
    rewrite List.firstn_all in *;
    rewrite refines_trace_refl;
    reflexivity.
Qed.

Lemma regfile_eq_empty_false:
  forall st1 st,
    ~ Ir.Regfile.eq (st::st1) [].
Proof.
  intros.
  intros HEQ.
  unfold Ir.Regfile.eq in HEQ.
  destruct st.
  assert (H := HEQ n).
  unfold Ir.Regfile.get in H.
  simpl in H. rewrite PeanoNat.Nat.eqb_refl in H. inv H.
Qed.

Theorem refines_regfile_eq:
  forall st1 st2 (HEQ:Ir.Regfile.eq st1 st2),
    refines_regfile st1 st2.
Proof.
  intros.
  unfold Ir.Regfile.eq in HEQ.
  unfold refines_regfile.
  intros.
  assert (HEQ' := HEQ regid).
  split.
  { split; intros; congruence. }
  { intros.
    eexists. rewrite HEQ' in HGET. split. eassumption.
    eapply refines_value_refl. }
Qed.

Theorem refines_regfile_trans:
  forall st1 st2 st3
         (HREF1:refines_regfile st1 st2)
         (HREF2:refines_regfile st2 st3),
    refines_regfile st1 st3.
Proof.
  intros.
  unfold refines_regfile in *.
  unfold_all_ands_H.
  intros.
  assert (H1 := HREF1 regid).
  assert (H2 := HREF2 regid).
  unfold_all_ands_H.

  split.
  { 
    destruct H1. destruct H.
    split.
    { intros. apply H. apply H1. assumption. }
    { intros. apply H3. apply H4. assumption. }
  }
  intros.
  apply H2 in HGET.
  destruct HGET. destruct H3.
  apply H0 in H3. destruct H3. destruct H3.
  eexists. split. eassumption.
  eapply refines_value_trans. eassumption. ss.
Qed.

Theorem refines_stack_eq:
  forall st1 st2 (HEQ:Ir.Stack.eq st1 st2),
    refines_stack st1 st2.
Proof.
  intros.
  generalize dependent st1.
  induction st2.
  { intros. destruct st1. constructor.
    inv HEQ. }
  { intros.
    destruct st1. inv HEQ.
    inv HEQ.
    inv H2. inv H0.
    constructor.
    { split.  congruence. split. congruence.
      apply refines_regfile_eq. assumption. }
    eapply Forall2_implies.
    eapply H4.
    { intros.
      destruct x. destruct y. simpl in *.
      inv H0. inv H5. split. congruence. split. congruence.
      apply refines_regfile_eq. assumption.
    }
  }
Qed.

Theorem refines_stack_trans:
  forall st1 st2 st3
         (HREF1:refines_stack st1 st2)
         (HREF1:refines_stack st2 st3),
    refines_stack st1 st3.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent st3.
  induction st1.
  { intros. inv HREF1. assumption. }
  { intros.
    destruct st2. inv HREF1.
    destruct st3. inv HREF0.
    inv HREF1. inv HREF0.
    unfold_all_ands_H.
    constructor.
    { split. congruence. split. congruence.
      eapply refines_regfile_trans. eassumption. ss. }
    { eapply Forall2_trans.
      intros.
      unfold_all_ands_H.
      split. congruence. split. congruence.
      eapply refines_regfile_trans. eassumption. ss.
      eassumption. ss.
    }
  }
Qed.

Theorem refines_state_eq:
  forall st1 st2 (HEQ:Ir.Config.eq st1 st2),
    refines_state st1 st2.
Proof.
  intros.
  inv HEQ.
  split.
  { rewrite H. eapply refines_memory_refl. }
  inv H0. split.
  apply refines_stack_eq. assumption.
  assumption.
Qed.

Theorem refines_refl:
  forall (pb:Ir.program_behavior), refines pb pb = true.
Proof.
  intros.
  destruct pb; unfold refines.
  - rewrite refines_trace_refl.
    rewrite refines_value_refl. reflexivity.
  - rewrite refines_trace_refl. reflexivity.
  - rewrite refines_trace_refl. reflexivity.
  - rewrite refines_trace_prefix_refl. reflexivity.
Qed.

Theorem refines_trace_none:
  forall (t1 t2:Ir.trace)
         (HREF:refines_trace t1 t2 = true),
    refines_trace (Ir.e_none::t1) t2 = true.
Proof. intros. unfold refines_trace in *.
       simpl. assumption.
Qed.

Theorem refines_trace_none2:
  forall (t1 t2:Ir.trace)
         (HREF:refines_trace t1 t2 = true),
    refines_trace t1 (Ir.e_none::t2) = true.
Proof. intros. unfold refines_trace in *.
       simpl. assumption.
Qed.


End Refinement.

End Ir.
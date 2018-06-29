Require Import Common.
Require Import State.
Require Import Value.
Require Import BinNat.
Require Import Memory.
Require Import sflib.
Require Import Omega.

(* This file defines what a program behavior is. *)


Module Ir.

Inductive event :=
| e_none: event
| e_some (n:N): event.

Definition not_none (e:event): bool :=
  match e with
  | e_none => false
  | _ => true
  end.

(* Trace is a list of events. *)
Definition trace := list event.

(* Excerpted from CompCert's behavior definition, with following changes:
   - No infinite event list ('Reacts' constructor)
   - Have OOM
   *)
Inductive program_behavior :=
| b_terminates: trace -> Ir.val -> program_behavior (* have a finite trace, and terminates with a value *)
| b_diverges: trace -> program_behavior (* diverge with a finite trace of observable events. *)
| b_goes_wrong: trace -> program_behavior (* a program gets stuck, i.e., has undefined behavior *)
| b_oom: trace -> program_behavior (* a program raises out-of-memory. *)
.


Definition refines_value (v_tgt v_src:Ir.val): bool :=
  match (v_tgt, v_src) with
  | (_, Ir.poison) => true
  | (Ir.num ntgt, Ir.num nsrc) => N.eqb ntgt nsrc
  | (Ir.ptr ptgt, Ir.ptr psrc) => Ir.ptr_eqb ptgt psrc
  | (_, _) => false
  end.

Definition refines_event (e_tgt e_src:event): bool :=
  match (e_tgt, e_src) with
  | (e_some vtgt, e_some vsrc) => N.eqb vtgt vsrc
  | (e_none, e_none) => true
  | _ => false
  end.

Definition refines_trace (tr_tgt tr_src:trace):bool :=
  let tr_tgt' := List.filter not_none tr_tgt in
  let tr_src' := List.filter not_none tr_src in
  if Nat.eqb (List.length tr_tgt') (List.length tr_src') then
    List.forallb (fun ee => refines_event ee.(fst) ee.(snd))
                 (List.combine tr_tgt' tr_src')
  else false.

(* If tgts_prefix is true, check whether tr_tgt has a prefix
   that refines tr_src.
   If tgts_prefix is false, check whether tr_src has a prefix
   so tr_tgt refines the prefix. *)
Definition refines_trace_prefix (tr_tgt tr_src:trace) (tgts_prefix:bool)
: bool :=
  let tr_tgt' := List.filter not_none tr_tgt in
  let tr_src' := List.filter not_none tr_src in
  let (tr_tgt', tr_src') :=
      if tgts_prefix then (List.firstn (List.length tr_src') tr_tgt', tr_src')
      else (tr_tgt', List.firstn (List.length tr_tgt') tr_src') in
  refines_trace tr_tgt' tr_src'.


(* Checks whether the behavior of a target program refines the behavior of a source program. *)
Definition refines (pb_tgt pb_src:program_behavior):bool :=
  match (pb_tgt, pb_src) with
  | (b_terminates tr_tgt ret_tgt, b_terminates tr_src ret_src) =>
    refines_trace tr_tgt tr_src && refines_value ret_tgt ret_src

  | (b_terminates tr_tgt ret_tgt, b_diverges tr_src) =>
    (* infinite loop without any event is UB.
       Chech whether target's trace has a prefix that refines trace of the source. *)
    refines_trace_prefix tr_tgt tr_src true

  | (b_terminates tr_tgt ret_tgt, b_goes_wrong tr_src) =>
    refines_trace_prefix tr_tgt tr_src true

  | (b_diverges tr_tgt, b_diverges tr_src) =>
    refines_trace tr_tgt tr_src

  | (b_diverges tr_tgt, b_goes_wrong tr_src) =>
    refines_trace tr_tgt tr_src

  | (b_goes_wrong tr_tgt, b_diverges tr_src) =>
    refines_trace tr_tgt tr_src

  | (b_goes_wrong tr_tgt, b_goes_wrong tr_src) =>
    refines_trace tr_tgt tr_src

  | (b_oom tr_tgt, b_terminates tr_src ret_src) =>
    refines_trace_prefix tr_tgt tr_src false

  | (b_oom tr_tgt, b_diverges tr_src) =>
    (* If source has UB and target has OOM,
       either the trace of source may be the prefix of the trace of target,
       or the trace of target may be the prefix of the trace of source. *)
    refines_trace_prefix tr_tgt tr_src true ||
    refines_trace_prefix tr_tgt tr_src false

  | (b_oom tr_tgt, b_goes_wrong tr_src) =>
    refines_trace_prefix tr_tgt tr_src true ||
    refines_trace_prefix tr_tgt tr_src false

  | (b_oom tr_tgt, b_oom tr_src) =>
    (* target trace should be prefix of source trace. *)
    refines_trace_prefix tr_tgt tr_src true

  | (_, _) => false
  end.



Theorem refines_value_refl:
  forall (v:Ir.val), refines_value v v = true.
Proof.
  intros.
  destruct v; unfold refines_value.
  - rewrite N.eqb_eq. auto.
  - rewrite Ir.ptr_eqb_refl. reflexivity.
  - reflexivity.
Qed.

Theorem refines_event_refl:
  forall (e:event), refines_event e e = true.
Proof.
  intros.
  destruct e. unfold refines_event. reflexivity.
  unfold refines_event. rewrite N.eqb_eq. reflexivity.
Qed.

Theorem refines_trace_refl:
  forall (t:trace), refines_trace t t = true.
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
    destruct (not_none a) eqn:HNN.
    simpl. rewrite IHt. rewrite refines_event_refl. reflexivity.
    assumption.
Qed.

Theorem refines_trace_prefix_refl:
  forall (t:trace) b, refines_trace_prefix t t b = true.
Proof.
  intros.
  destruct b; unfold refines_trace_prefix in *;
    rewrite List.firstn_all in *;
    rewrite refines_trace_refl;
    reflexivity.
Qed.

Theorem refines_refl:
  forall (pb:program_behavior), refines pb pb = true.
Proof.
  intros.
  destruct pb; unfold refines.
  - rewrite refines_trace_refl.
    rewrite refines_value_refl. reflexivity.
  - rewrite refines_trace_refl. reflexivity.
  - rewrite refines_trace_refl. reflexivity.
  - rewrite refines_trace_prefix_refl. reflexivity.
Qed.

End Ir.
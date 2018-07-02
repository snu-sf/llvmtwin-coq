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

(***********************************************************
   Propositional definition of refinements on memory, state
 ***********************************************************)

Definition refines_memblock (mb_tgt mb_src:Ir.MemBlock.t) :=
  mb_tgt.(Ir.MemBlock.bt) = mb_src.(Ir.MemBlock.bt) /\
  mb_tgt.(Ir.MemBlock.r) = mb_src.(Ir.MemBlock.r) /\
  mb_tgt.(Ir.MemBlock.n) = mb_src.(Ir.MemBlock.n) /\
  mb_tgt.(Ir.MemBlock.a) = mb_src.(Ir.MemBlock.a) /\
  List.Forall2 refines_byte mb_tgt.(Ir.MemBlock.c) mb_src.(Ir.MemBlock.c) /\
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

(* Note that refines_state does not compare two modules. *)
Definition refines_state (s_tgt s_src:Ir.Config.t) :=
  refines_memory s_tgt.(Ir.Config.m) s_src.(Ir.Config.m) /\
  refines_stack s_tgt.(Ir.Config.s) s_src.(Ir.Config.s) /\
  s_tgt.(Ir.Config.cid_to_f) = s_src.(Ir.Config.cid_to_f) /\
  s_tgt.(Ir.Config.cid_fresh) = s_src.(Ir.Config.cid_fresh).
(* Want to show:
   (1) if target state t and source state s are related,
   and source & target have same instructions to execute,
       equivalent, final states after execution



(***********************************************************
               Lemmas about refinement.
 ***********************************************************)

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

Theorem refines_trace_none:
  forall (t1 t2:trace)
         (HREF:refines_trace t1 t2 = true),
    refines_trace (e_none::t1) t2 = true.
Proof. intros. unfold refines_trace in *.
       simpl. assumption.
Qed.

Theorem refines_trace_none2:
  forall (t1 t2:trace)
         (HREF:refines_trace t1 t2 = true),
    refines_trace t1 (e_none::t2) = true.
Proof. intros. unfold refines_trace in *.
       simpl. assumption.
Qed.

End Ir.
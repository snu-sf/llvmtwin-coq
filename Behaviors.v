Require Import Common.
Require Import State.
Require Import Value.
Require Import BinNat.

(* Defines what a program behavior is. *)

Module Ir.

Inductive event :=
| e_none: event
| e_some (v:Ir.val): event.

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


Definition refines_trace (tr_tgt tr_src:trace) :=
  

(* Checks whether the behavior of a target program refines the behavior of a source program. *)
Definition refines (pb_tgt pb_src:program_behavior):bool :=
  match (pb_tgt, pb_src) with
  | (b_terminates tr_tgt ret_tgt, b_terminates tr_src ret_src) =>
    refines_trace tr_tgt tr_src && refines_val ret_tgt ret_src

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
    refines_trace_prefix tr_tgt tr_src

  | (_, _) => false
  end.

End Ir.
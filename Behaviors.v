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
| e_some (n:nat): event.

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



End Ir.
Require Import BinNat.
Require Import Bool.
Require Import List.

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

(* Is it valid to reorder 'i1;i2' into 'i2;i1'? *)
Definition inst_reorderable_unidir (i1 i2:Ir.Inst.t): Prop :=
  (* If there's no data dependency from i1 to i2 *)
  forall (HNODEP:has_data_dependency i1 i2 = false),
    (* 'i1;i2' -> 'i2;i1' is allowed *)
    forall (st0 st1 st2:Ir.Config.t) (* Initial state, state after i1, state after 'i1;i2' *)
           (e1 e2:Ir.event) (* i1's event, i2's event *)
           (HWF:Ir.Config.wf st0) (* Well-formedness of st0 *)
           (HSTEP1:Ir.SmallStep.inst_step st0 i1 (Ir.SmallStep.sr_success e1 st1))
           (HSTEP2:Ir.SmallStep.inst_step st1 i2 (Ir.SmallStep.sr_success e2 st2)),
      exists st1' st2' (* state after i2, state after 'i2;i1' *)
             e1' e2', (* i2's event, i1's event *)
        Ir.SmallStep.inst_step st0  i2 (Ir.SmallStep.sr_success e1' st1') /\
        Ir.SmallStep.inst_step st1' i1 (Ir.SmallStep.sr_success e2' st2') /\
        st2 = st2' /\ (* Final state is the same *)
        (* Has same event sequence as well. *)
        List.filter (Ir.not_none) (e1::e2::nil) = List.filter (Ir.not_none) (e1'::e2'::nil).

(* 'i1;i2 <-> i2;i1'. *)
Definition inst_reorderable (i1 i2:Ir.Inst.t): Prop :=
  inst_reorderable_unidir i1 i2 /\ inst_reorderable_unidir i2 i1.





(* Reordering between ptrtoint/ptrtoint:

   r1 = ptrtoint opptr1 ty1;
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2;
   r1 = ptrtoint opptr1 ty1
*)
(*
Lemma reorder_unidir_ptrtoint_ptrtoint:
  forall i1 i2 r1 r2 opptr1 opptr2 ty1 ty2
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 ty1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 ty2),
    inst_reorderable_unidir i1 i2.
*)
  

End Reordering.

End Ir.
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

(* Analogous to Ir.SmallStep.incrpc, except that it returns None if there's no
   trivial next pc. *)
Definition incrpc' (c:Ir.Config.t):option Ir.Config.t :=
  match (Ir.Config.cur_fdef_pc c) with
  | Some (fdef, pc0) =>
    match (Ir.IRFunction.next_trivial_pc pc0 fdef) with
    | Some pc' =>
      Some (Ir.Config.update_pc c pc')
    | None => None (* Cannot happen..! *)
    end
  | None => None (* Cannot happen *)
  end.

Definition inst_locates_at (c:Ir.Config.t) (i1 i2:Ir.Inst.t):Prop :=
  exists c',
    Ir.Config.cur_inst c = Some i1 /\
    Some c' = incrpc' c /\
    Ir.Config.cur_inst c' = Some i2.


(* Is it valid to reorder 'i1;i2' into 'i2;i1'? *)
Definition inst_reorderable_unidir (i1 i2:Ir.Inst.t): Prop :=
  (* If there's no data dependency from i1 to i2 *)
  forall (HNODEP:has_data_dependency i1 i2 = false),
    (* 'i1;i2' -> 'i2;i1' is allowed *)
    forall (st st':Ir.Config.t) (* Initial state, state after 'i1;i2' *)
           (HWF:Ir.Config.wf st) (* Well-formedness of st0 *)
           (HLOCATE:inst_locates_at st i1 i2)
           (HSTEP:Ir.SmallStep.inst_nstep st 2 sr),
      exists st'' (* state after 'i2;i1' *)
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
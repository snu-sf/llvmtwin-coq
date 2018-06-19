Require Import Common.
Require Import Syntax.
Require Import List.


Module Ir.

(****************************************
        Dominatedness relation.
 ***************************************)

Definition dominates (from to:Ir.IRFunction.pc) (f:Ir.IRFunction.t) :=
  forall (exec:list Ir.IRFunction.pc)
         (HVALID: forall_adj
                    (fun pc pc_next => Ir.IRFunction.valid_next_pc pc pc_next f)
                    (exec ++ (to::nil)) = true),
    List.In from (exec ++ (to::nil)).

(* Theorem: reflexivity of dominatedness. *)
Theorem dominates_refl:
  forall (pc:Ir.IRFunction.pc) (f:Ir.IRFunction.t),
    dominates pc pc f.
Proof.
  intros.
  unfold dominates.
  intros.
  rewrite in_rev.
  rewrite rev_unit.
  constructor. reflexivity.
Qed.


Structure welltyped (m:Ir.IRModule.t) :=
  {
    ssa:forall (f:Ir.IRFunction.t)
               (HFIN:List.In f m)
               (r:Ir.reg),
      List.length (Ir.IRFunction.get_defs r f) < 2;
    
  }.

End Ir.
Require Import Common.
Require Import Lang.
Require Import List.


Module Ir.

(****************************************
        Dominatedness relation.
 ***************************************)

Definition dominates (from to:Ir.IRFunction.pc) (f:Ir.IRFunction.t) :=
  forall (exec:list Ir.IRFunction.pc)
         (HLEN:List.length exec > 0)
         (HBEGIN:List.hd from exec = Ir.IRFunction.get_begin_pc f)
         (HEND:List.last exec to = to)
         (HVALID: forall_adj
                    (fun pc pc_next => Ir.IRFunction.valid_next_pc pc pc_next f)
                    exec = true),
    List.In from exec.

(* Theorem: reflexivity of dominatedness. *)
Theorem dominates_refl:
  forall (pc:Ir.IRFunction.pc) (f:Ir.IRFunction.t),
    dominates pc pc f.
Proof.
  intros.
  unfold dominates.
  intros.
  destruct exec.
  simpl in HLEN. inversion HLEN.
  simpl in HBEGIN.

  apply last_head in HEND.
  remember (rev (p::exec)) as l.
  assert (List.length l = List.length (p::exec)).
  { rewrite Heql. rewrite rev_length. reflexivity. }
  destruct l.
  - simpl in H. inversion H.
  - simpl in HEND.
    assert (p :: exec = rev (p0::l)).
    { rewrite Heql. rewrite rev_involutive. reflexivity. }
    rewrite H0.
    apply in_rev. rewrite rev_involutive. rewrite HEND. constructor.
    reflexivity.
  - simpl.
    apply Gt.gt_Sn_O.
Qed.


Structure welltyped (m:Ir.IRModule.t) :=
  {
    ssa:forall (f:Ir.IRFunction.t)
               (HFIN:List.In f m)
               (r:Ir.reg),
      List.length (Ir.IRFunction.get_defs r f) < 2;
    
  }.

End Ir.
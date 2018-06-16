Require Import List.
Require Import BinPos.

Inductive list_has {X:Type}: X -> list X -> Prop :=
| lh_one: forall (a:X) (l:list X), list_has a (a::l)
| lh_cons: forall (a b:X) (l:list X), list_has a l -> list_has a (b::l).


(* Definition of disjointness. *)

Definition disjoint_range (r1 r2:nat * nat): bool :=
  match (r1, r2) with
  | ((b1, len1), (b2, len2)) =>
    Nat.leb (b1 + len1) b2 || Nat.leb (b2 + len2) b1
  end.

Fixpoint disjoint_ranges (rs:list (nat*nat)): bool :=
  match rs with
  | nil => true
  | r::t => List.forallb (fun r2 => disjoint_range r r2) t && disjoint_ranges t
  end.

Theorem disjoint_startidx_one



Fixpoint pos_to_bits (n:positive): list bool :=
  match n with
  | xH => true::nil
  | xI n' => true::(pos_to_bits n')
  | xO n' => false::(pos_to_bits n')
  end.
Definition N_to_bits (n:N): list bool :=
  match n with
  | N0 => nil
  | Npos p => pos_to_bits p
  end.

Eval compute in N_to_bits 0%N. (* nil *)
Eval compute in N_to_bits 10%N. (* [f,t,f,t] *)

Fixpoint bits_to_pos (bits:list bool): positive :=
  match bits with
  | nil => xH
  | true::nil => xH
  | h::t => (if h then xI else xO) (bits_to_pos t)
  end.
Fixpoint bits_to_N (bits:list bool): N :=
  match bits with
  | nil => N0
  | _ => Npos (bits_to_pos bits)
  end.


Fixpoint erase_lzerobits (bits:list bool): list bool :=
  match bits with
  | nil => nil
  | h::t =>
    match h with | false => erase_lzerobits t | true => bits
    end
  end.

Definition erase_hzerobits (bits:list bool): list bool :=
  List.rev (erase_lzerobits (List.rev bits)).

Eval compute in bits_to_N nil. (* 0 *)
Eval compute in bits_to_N (true::false::true::nil). (* 5 *)
Eval compute in erase_hzerobits (false::false::true::false::nil).


Lemma pos_bits_pos:
  forall (p:positive), bits_to_pos (pos_to_bits p) = p.
Proof.
  intros.
  induction p.
  - simpl. rewrite IHp.
    destruct p; simpl; reflexivity.
  - simpl. rewrite IHp. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma N_bits_N:
  forall (n:N), bits_to_N (N_to_bits n) = n.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - simpl.
    assert (~ (pos_to_bits p = nil)).
    {
      intros H.
      destruct p; simpl in H; inversion H.
    }
    destruct (pos_to_bits p) eqn:HEQ.
    + exfalso. apply H. reflexivity.
    + unfold bits_to_N. rewrite <- HEQ. rewrite pos_bits_pos. reflexivity.
Qed.

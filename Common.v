Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import Coq.Arith.PeanoNat.

(* Definition of list subseq. *)

Inductive lsubseq {X:Type}: list X -> list X -> Prop :=
| ss_nil: lsubseq nil nil
| ss_cons: forall (x:X) (l1 l2:list X) (H:lsubseq l1 l2),
    lsubseq (x::l1) (x::l2)
| ss_elon: forall (x:X) (l1 l2:list X) (H:lsubseq l1 l2),
    lsubseq (x::l1) l2.

Lemma lsubseq_refl: forall {X:Type} (l:list X), lsubseq l l.
Proof.
  intros.
  induction l. constructor. constructor. assumption.
Qed.

Lemma lsubseq_filter: forall {X:Type} (l:list X) f,
    lsubseq l (List.filter f l).
Proof.
  intros.
  induction l. constructor. simpl.
  destruct (f a) eqn:H. constructor. assumption.
  constructor. assumption.
Qed.

Lemma lsubseq_forallb: forall {X:Type} (l l':list X) f
                             (H:List.forallb f l = true)
                             (HLSS:lsubseq l l'),
    List.forallb f l' = true.
Proof.
  intros.
  induction HLSS.
  - assumption.
  - simpl in *.
    rewrite andb_true_iff in *.
    destruct H.
    split. assumption. apply IHHLSS. assumption.
  - simpl in H. rewrite andb_true_iff in H.
    destruct H. apply IHHLSS. assumption.
Qed.

(* the result of List.filter satisfies forallb. *)
Lemma filter_forallb: forall {X:Type} (l:list X) f,
    List.forallb f (List.filter f l) = true.
Proof.
  intros.
  induction l. reflexivity. simpl.
  destruct (f a) eqn:H. simpl. rewrite H. rewrite IHl. auto.
  assumption.
Qed.

(*******************************************
      Definition of range & disjointness.
 *******************************************)

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

Definition in_range (i:nat) (r:nat * nat): bool :=
  Nat.leb r.(fst) i && Nat.leb i (r.(fst) + r.(snd)).

Definition disjoint_include (rs:list (nat * nat)) (i:nat): list (nat*nat) :=
  List.filter (in_range i) rs.

Definition no_empty_range (rs:list (nat * nat)): bool :=
  List.forallb (fun t => Nat.ltb 0 t.(snd)) rs.



(* Lemma: the subsequence of disjoint ranges is also disjoint. *)
Lemma disjoint_lsubseq_disjoint:
  forall rs rs'
         (HDISJ:disjoint_ranges rs = true)
         (HLSS:lsubseq rs rs'),
    disjoint_ranges rs' = true.
Proof.
  intros.
  induction HLSS.
  - assumption.
  - simpl in *.
    rewrite andb_true_iff in *.
    destruct HDISJ as [HDISJ1 HDISJ2].
    split.
    + apply lsubseq_forallb with (l := l1).
      assumption.
      assumption.
    + apply IHHLSS. assumption.
  - simpl in HDISJ.
    rewrite andb_true_iff in HDISJ.
    destruct HDISJ as [_ HDISJ].
    apply IHHLSS. assumption.
Qed.

(* Lemma: the result of disjoint_include is subsequence of the input. *)
Lemma disjoint_include_lsubseq:
  forall rs i, lsubseq rs (disjoint_include rs i).
Proof.
  intros. unfold disjoint_include. apply lsubseq_filter.
Qed.

(* Lemma: If there are three ranges (b1, l1), (b2, l2), (b3, l3),
   and they all include some natural number i,
   (e.g. b1<=i<=l1, b2<=i<=l2, b3<=i<=l3),
   and l1 != 0 && l2 != 0 && l3 != 0,
   the three ranges cannot be disjoint. *)
Lemma inrange3_never_disjoint:
  forall (r1 r2 r3:nat * nat) i
         (H1:in_range i r1 = true)
         (H2:in_range i r2 = true)
         (H3:in_range i r3 = true)
         (HNOEMPTY:no_empty_range (r1::r2::r3::nil) = true),
    disjoint_ranges (r1::r2::r3::nil) = false.
Proof.
  intros.
  unfold in_range in *.
  destruct r1 as [b1 l1].
  destruct r2 as [b2 l2].
  destruct r3 as [b3 l3].
  simpl in *.
  rewrite andb_true_r in *.
  repeat (rewrite andb_true_r).
  repeat (rewrite andb_true_iff in *).
  destruct H1. destruct H2. destruct H3.
  destruct HNOEMPTY.
  destruct H6.
  destruct (disjoint_range (b1, l1) (b2, l2)) eqn:HDR1;
  destruct (disjoint_range (b1, l1) (b3, l3)) eqn:HDR2;
  destruct (disjoint_range (b2, l2) (b3, l3)) eqn:HDR3;
  try auto.

  assert (HTRI:forall x y z
                 (H1:Nat.ltb x y = true)
                 (H2:Nat.ltb y z = true)
                 (H3:Nat.ltb z x = true), False).
  {
    intros.
    rewrite Nat.ltb_lt in *.
    assert (x < z). apply Nat.lt_trans with (m := y); assumption.
    apply (Nat.lt_asymm x z H11).
    assumption.
  }
  (* remains only one case! - when all disjoint_range return true *)
  unfold disjoint_range in *.
  rewrite orb_true_iff in *.
  destruct HDR1; destruct HDR2; destruct HDR3; exfalso.
Admitted.

(* Theorem: If ranges are disjoint, there at most 2 ranges
   which contain number i. *)
Theorem disjoint_includes_atmost_2:
  forall rs i rs' (HDISJ: disjoint_ranges rs = true)
         (HIN:rs' = disjoint_include rs i)
         (HNOZERO:no_empty_range rs = true),
    List.length rs' < 3.
Proof.
  intros.
  generalize dependent rs'.
  induction rs.
  - intros. simpl in HIN. rewrite HIN. simpl. auto.
  - intros.
    simpl in HDISJ.
    rewrite andb_true_iff in HDISJ. 
    simpl in HNOZERO.
    rewrite andb_true_iff in HNOZERO.
    destruct HDISJ as [HDISJ1 HDISJ2].
    destruct HNOZERO as [HNOZERO1 HNOZERO2].
    simpl in HIN.
    destruct (in_range i a) eqn:HCOND.
    + (* New element fit. *)
      (* rs' is an updated range. *)
      destruct rs' as [| rs'h rs't].
      * inversion HIN.
      * inversion HIN.
        rewrite <- H0 in *.
        clear H0.
        destruct rs'h as [beg len].
        simpl in HCOND.
        assert (length rs't < 3).
        {
          apply IHrs; assumption.
        }
        (* rs't may be [], [(beg1,len1)], [(beg1,len1),(beg2,len2)]. *)
        destruct rs't as [ | rs'th rs'tt].
        { rewrite <- H1. simpl. auto. } (* [] *)
        destruct rs'th as [beg1 len1].
        destruct rs'tt as [ | rs'tth rs'ttt].
        { rewrite <- H1. simpl. auto. } (* [(beg1, len1)] *)
        destruct rs'tth as [beg2 len2].
        destruct rs'ttt as [ | rs'ttth rs'tttt].
        { (* [(beg1, len1), (beg2, len2)]. *)
          (* (beg1, len1), (beg2, len2) are in rs(all ranges) as well. *)
          admit.
        }
Admitted.


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

Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Sumbool.
Require Import Basics.
Require Import Omega.


(* Some helpful lemmas regarding List *)

(* If List.length l = 1, l = h::nil. *)
Lemma list_len1:
  forall {X:Type} (l:list X)
         (H:List.length l = 1),
    exists h, l = h::nil.
Proof.
  intros.
  destruct l.
  - simpl in H. inversion H.
  - destruct l.
    + eexists. reflexivity.
    + simpl in H. inversion H.
Qed.

(* If List.length l = 2, l = h1::h2::nil. *)
Lemma list_len2:
  forall {X:Type} (l:list X)
         (H:List.length l = 2),
    exists h1 h2, l = h1::h2::nil.
Proof.
  intros.
  destruct l.
  - simpl in H. inversion H.
  - destruct l.
    + simpl in H. inversion H.
    + destruct l.
      * eexists. eexists. reflexivity.
      * simpl in H. inversion H.
Qed.

Lemma firstn_app_decompose {X:Type}:
  forall (l l1 l2:list X) n
         (HL:l = l1 ++ l2)
         (HLEN:List.length l1 = n),
    firstn n l = l1.
Proof.
  intros.
  generalize dependent l.
  generalize dependent n.
  induction l1.
  - simpl. intros. rewrite <- HLEN. reflexivity.
  - simpl. intros.
    destruct n.
    + inversion HLEN.
    + inversion HLEN.
      destruct l.
      inversion HL.
      inversion HL.
      simpl. rewrite H0. rewrite IHl1. reflexivity.
      congruence. reflexivity.
Qed.

Lemma skipn_app_decompose {X:Type}:
  forall (l l1 l2:list X) n
         (HL:l = l1 ++ l2)
         (HLEN:List.length l1 = n),
    skipn n l = l2.
Proof.
  intros.
  generalize dependent l.
  generalize dependent n.
  induction l1.
  - simpl. intros. rewrite HL. rewrite <- HLEN. reflexivity.
  - simpl. intros.
    destruct n.
    + inversion HLEN.
    + inversion HLEN.
      destruct l.
      inversion HL.
      inversion HL.
      simpl. rewrite H0. rewrite IHl1. reflexivity.
      congruence. reflexivity.
Qed.

Lemma skipn_all {X:Type}:
  forall (l:list X) n
         (HLEN:List.length l <= n),
    skipn n l = nil.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - simpl. intros. destruct n; reflexivity.
  - simpl. intros.
    destruct n.
    + inversion HLEN.
    + simpl. apply IHl.
      apply le_S_n. assumption.
Qed.

Lemma app_decompose {X:Type} (n:nat):
  forall (l:list X)
         (HLEN:n <= List.length l),
    exists l1 l2, (l = l1 ++ l2 /\ List.length l1 = n).
Proof.
  intros.
  generalize dependent n.
  induction l.
  - simpl. intros. inversion HLEN.
    exists nil. exists nil. split; reflexivity.
  - simpl. intros.
    destruct n.
    + exists nil. exists (a::l). split; reflexivity.
    + apply le_S_n in HLEN.
      apply IHl in HLEN.
      destruct HLEN. destruct H.
      destruct H.
      exists (a::x). exists x0.
      rewrite H. split. reflexivity. simpl. congruence.
Qed.

Lemma firstn_firstn_skipn {X:Type}:
  forall n1 n2 (l:list X),
    firstn n1 l ++ firstn n2 (skipn n1 l) = firstn (n1+n2) l.
Proof.
  intros.
  assert (HD := app_decompose n1 l).
  assert (HDEC := Compare_dec.le_gt_dec n1 (List.length l)).
  destruct HDEC as [HDEC | HDEC].
  - apply HD in HDEC.
    destruct HDEC as [l1 [l2 [HDEC1 HDEC2]]].
    rewrite firstn_app_decompose with (l0 := l) (l3 := l1) (l4 := l2).
    rewrite <- HDEC2.
    rewrite HDEC1.
    rewrite firstn_app_2.
    rewrite skipn_app_decompose with (l3 := l1) (l4 := l2).
    reflexivity. reflexivity. reflexivity. congruence. congruence.
  - assert (length l <= n1).
    { apply Gt.gt_le_S in HDEC.
      apply PeanoNat.Nat.le_trans with (m := S (length l)).
      auto. assumption. }
    rewrite firstn_all2.
    rewrite firstn_all2 with (n:= n1+n2).
    rewrite skipn_all. rewrite firstn_nil.
    rewrite app_nil_r. reflexivity.
    assumption.
    apply Gt.gt_le_S in HDEC.
    apply PeanoNat.Nat.le_trans with (m := n1).
    apply PeanoNat.Nat.le_trans with (m := S (length l)).
    auto. assumption. apply PeanoNat.Nat.le_add_r.
    assumption.
Qed.


(* If the result of List.combine is nil, and
   their length is the same. input is both nil *)
Lemma combine_length_nil:
  forall {X Y:Type} (l1: list X) (l2:list Y)
         (HLEN:List.length l1 = List.length l2)
         (HNIL:List.combine l1 l2 = nil),
    l1 = nil /\ l2 = nil.
Proof.
  intros.
  destruct l1; destruct l2.
  - split; reflexivity.
  - simpl in HLEN. inversion HLEN.
  - simpl in HLEN. inversion HLEN.
  - simpl in HNIL. inversion HNIL.
Qed.

Lemma combine_length_some:
  forall {X Y:Type} (l1: list X) (l2:list Y) a t
         (HLEN:List.length l1 = List.length l2)
         (HSOME:List.combine l1 l2 = a::t),
    l1 = (a.(fst))::((List.split t).(fst))  /\
    l2 = (a.(snd))::((List.split t).(snd)).
Proof.
  intros.
  assert (split (combine l1 l2) = (l1, l2)).
  { apply combine_split. assumption. }
  destruct l1; destruct l2.
  - simpl in HSOME; inversion HSOME. 
  - simpl in HLEN; inversion HLEN.
  - simpl in HLEN; inversion HLEN.
  - simpl in HSOME.
    inversion HSOME.
    simpl in H.
    remember (split (combine l1 l2)) as q.
    destruct q.
    inversion H.
    simpl.
    split; reflexivity.
Qed.

(* l = combine (fst (split l), snd (split l)). *)
Lemma combine_fst_snd_split:
  forall {X Y:Type} (l:list (X*Y)),
    l = List.combine (fst (List.split l)) (snd (List.split l)).
Proof.
  intros.
  induction l.
  - reflexivity.
  - destruct a.
    remember (split l) as p.
    simpl.
    rewrite <- Heqp.
    destruct p.
    simpl. rewrite IHl.
    reflexivity.
Qed.

Lemma combine_map_In:
  forall {X Y:Type} (ly:list Y) (f:Y -> X) (x:X) (y:Y) (lx:list X)
         (HX:x = f y)
         (HLX:lx = List.map f ly)
         (HIN:List.In y ly),
  List.In (x, y) (List.combine lx ly).
Proof.
  induction ly.
  - intros. simpl in HIN. inversion HIN.
  - simpl. intros.
    destruct lx; inversion HLX.
    simpl.
    rewrite HX.
    destruct HIN.
    + left. congruence.
    + right. apply IHly with (f := f).
      reflexivity. reflexivity. assumption.
Qed.

(* Filtered list is shorter than the original list. *)
Lemma filter_length:
  forall {X:Type} (l:list X) f,
    List.length (List.filter f l) <= List.length l.
Proof.
  intros.
  induction l.
  - simpl. auto.
  - simpl.
    destruct (f a).
    + simpl.
      apply Le.le_n_S.
      assumption.
    + apply le_S.
      assumption.
Qed.

Lemma app_equal {X:Type}:
  forall (l1' l2' l1 l2:list X) (x x':X)
         (HNOTIN1:~List.In x' l1)
         (HNOTIN1':~List.In x l1')
         (HEQ:l1' ++ x' :: l2' = l1 ++ x :: l2),
    l1 = l1' /\ l2 = l2' /\ x' = x.
Proof.
  intros.
  generalize dependent l1'.
  induction l1.
  - intros. simpl in HEQ.
    destruct l1'. simpl in HEQ.
    inversion HEQ. split. reflexivity. split; congruence.
    simpl in HEQ. inversion HEQ. rewrite H0 in HNOTIN1'.
    exfalso. apply HNOTIN1'. constructor.
    reflexivity.
  - simpl. intros.
    destruct l1'.
    + simpl in HEQ. inversion HEQ. rewrite H0 in HNOTIN1.
      exfalso. apply HNOTIN1. constructor. reflexivity.
    + simpl in HEQ.
      inversion HEQ. rewrite H0 in *. clear H0.
      assert (l1 = l1' /\ l2 = l2' /\ x' = x).
      { apply IHl1. simpl in HNOTIN1.
        apply Decidable.not_or in HNOTIN1. destruct HNOTIN1. assumption.
        simpl in HNOTIN1'. apply Decidable.not_or in HNOTIN1'.
        destruct HNOTIN1'. assumption.
        assumption. }
      destruct H. destruct H0.
      split. congruence. split; congruence.
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

Lemma filter_app {X:Type}:
  forall (l1 l2:list X) (f:X -> bool),
    List.filter f (l1++l2) = (List.filter f l1) ++ (List.filter f l2).
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. destruct (f a). rewrite IHl1. reflexivity.
    assumption.
Qed.

Lemma forallb_map:
  forall {X Y:Type} (l: list X) (l':list Y)
         (f:X -> Y) (g:Y -> bool) (h:X -> bool) b
         (HMAP:l' = List.map f l)
         (HFORALLB:forallb g l' = b)
         (HEQ:forall x, (compose g f) x = h x),
    forallb h l = b.
Proof.
  intros.
  generalize dependent l'.
  induction l.
  - simpl. intros. rewrite HMAP in *. simpl in HFORALLB. congruence.
  - simpl. intros. rewrite HMAP in HFORALLB.
    simpl in HFORALLB.
    destruct l'. inversion HMAP.
    inversion HMAP.
    unfold compose in *.
    destruct (g (f a)) eqn:HGF.
    + simpl. erewrite IHl. rewrite <- HEQ. rewrite HGF. reflexivity. eassumption.
      simpl in HFORALLB. rewrite H1. assumption.
    + simpl in HFORALLB. simpl. rewrite <- HEQ. rewrite HGF. simpl. assumption.
Qed.

Lemma forallb_implies:
  forall {X:Type} (l:list X) (f g:X -> bool)
         (HIMP:forall x, f x = true -> g x = true)
         (HFORALLB:List.forallb f l = true),
    List.forallb g l = true.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. simpl in HFORALLB.
    rewrite andb_true_iff in *.
    destruct HFORALLB.
    split. apply HIMP. assumption. apply IHl. assumption.
Qed.

Lemma split_map_fst:
  forall {X Y Z:Type} (l:list (X * Y)) (f:X * Y -> Z) (g:X -> Z)
         (HEQ:forall x y, f (x, y) = g x),
    List.map f l = List.map g (fst (split l)).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. destruct a.
  remember (split l) as p.
  destruct p.
  simpl in *.
  rewrite HEQ. congruence.
Qed.

Lemma split_map_snd:
  forall {X Y Z:Type} (l:list (X * Y)) (f:X * Y -> Z) (g:Y -> Z)
         (HEQ:forall x y, f (x, y) = g y),
    List.map f l = List.map g (snd (split l)).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. destruct a.
  remember (split l) as p.
  destruct p.
  simpl in *.
  rewrite HEQ. congruence.
Qed.

Lemma map_fst_split {X Y:Type}:
  forall (l:list (X * Y)),
    List.map fst l = (List.split l).(fst).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. destruct a.
    remember (split l) as p.
    destruct p. simpl. rewrite IHl. reflexivity.
Qed.

Lemma existsb_rev:
  forall {X:Type} (f:X -> bool) (l:list X),
    List.existsb f (List.rev l) = List.existsb f l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    rewrite existsb_app.
    simpl.
    rewrite orb_comm.
    rewrite orb_comm with (b1 := f a).
    simpl.
    rewrite IHl. reflexivity.
Qed.

(* Why do I need this? *)
Lemma list_eq:
  forall {X:Type} (a b:X) (c d:list X)
    (HEQ:a = b)
    (HEQ2:c = d),
    a::c = b::d.
Proof.
  intros.
  rewrite HEQ.
  rewrite HEQ2.
  reflexivity.
Qed.

(* If map f b = a,
   and p = split (filter g (combine a b)),
   map f p.snd = p.fst. *)
Lemma split_filter_combine_map:
  forall {X Y:Type} (a:list X) (b:list Y) p f g
         (HMAP:List.map f b = a)
         (HP:p = List.split (List.filter g (List.combine a b))),
    List.map f p.(snd) = p.(fst).
Proof.
  intros.
  remember (combine a b) as ab.
  generalize dependent a.
  generalize dependent b.
  generalize dependent p.
  induction ab as [| abh abt].
  - intros. simpl in HP. rewrite HP. reflexivity.
  - intros.
    destruct (split (filter g abt)) as [abtl abtr] eqn:HS.
    simpl in HP.
    destruct a as [| ah at'].
    { simpl in Heqab. inversion Heqab. }
    destruct b as [| bh bt].
    { simpl in Heqab. inversion Heqab. }
    destruct (g abh).
    + destruct abh as [abhl abhr].
      simpl in Heqab.
      inversion Heqab.
      rewrite H0 in *. clear H0.
      rewrite H1 in *. clear H1. clear Heqab.
      simpl in HP.
      rewrite HS in HP.
      rewrite HP.
      simpl.
      simpl in HMAP.
      inversion HMAP.
      rewrite H0 in *. clear H0.
      rewrite H1 in *. clear HMAP.
      apply list_eq. reflexivity.
      assert (abtr = snd (split (filter g abt))).
      { rewrite HS. reflexivity. }
      assert (abtl = fst (split (filter g abt))).
      { rewrite HS. reflexivity. }
      rewrite H. rewrite H0.
      eapply IHabt.
      * assumption.
      * apply H1.
      * assumption.
    + apply IHabt with (b := bt) (a := at').
      * rewrite HP. assumption.
      * simpl in HMAP.
        inversion HMAP. reflexivity.
      * simpl in Heqab.
        inversion Heqab.
        reflexivity.
Qed.

Lemma In_map:
  forall {X Y:Type} (l:list X) (f:X -> Y) (y:Y)
         (HIN:List.In y (List.map f l)),
    exists (x:X), f x = y /\ List.In x l.
Proof.
  induction l.
  intros. simpl in HIN. inversion HIN.
  intros.
  simpl in HIN.
  destruct HIN.
  - eexists. split. eassumption. constructor. reflexivity.
  - apply IHl in H.
    destruct H as [xH H].
    destruct H as [H1 H2].
    eexists.
    split. eassumption. simpl. right. assumption.
Qed.

Lemma In_notIn_neq {X:Type}:
  forall (l:list X) (x1 x2:X)
         (HNOTIN:~List.In x1 l)
         (HIN:List.In x2 l),
    x1 <> x2.
Proof.
  intros.
  intros HEQ.
  apply HNOTIN.
  congruence.
Qed.

Lemma last_cons {X:Type}:
  forall (l:list X) h h' h'',
    List.last (l ++ (h::nil)) h'' = List.last (h'::l ++ (h::nil)) h''.
Proof.
  intros.
  generalize dependent h'.
  induction l.
  - simpl. reflexivity.
  - intros. simpl. reflexivity.
Qed.

Lemma last_element {X:Type}:
  forall (l:list X) h1 h3 h2
         (HLAST:List.last (l ++ (h1::nil)) h3 = h2),
    h1 = h2.
Proof.
  intros.
  induction l.
  - simpl in HLAST. congruence.
  - simpl.
    replace ((a::l)++h1::nil) with (a::l++h1::nil) in HLAST.
    rewrite <- last_cons in HLAST.
    apply IHl. assumption.
    reflexivity.
Qed.

Lemma last_head {X:Type}:
  forall (l:list X) (HLEN:List.length l > 0) x
         (HLAST: List.last l x = x),
    List.hd x (List.rev l) = x.
Proof.
  intros.
  generalize dependent HLEN.
  generalize dependent HLAST.
  apply rev_ind with (l := l).
  - intros. simpl in HLEN. inversion HLEN.
  - intros.
    assert (x0 = x).
    { eapply last_element. eapply HLAST. }
    rewrite H0 in *.
    rewrite rev_unit.
    reflexivity.
Qed.

Lemma list_segmentize8_l {X:Type}:
  forall (bs:list X),
    exists b1 b2, bs = b1 ++ b2 /\
                  Nat.modulo (List.length b2) 8 = 0 /\
                  List.length b1 < 8.
Proof.
  intros.
  induction bs.
  - exists nil. eexists nil.
    split. reflexivity. split. reflexivity. simpl. omega.
  - inversion IHbs as [b1 [b2 IH]].
    destruct IH as [H1 [H2 H3]].
    destruct b1 as [ | h1 b1].
    { eexists (a::nil). eexists b2. 
      split. rewrite H1. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h2 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h3 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::h2::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h4 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::h2::h3::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h5 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::h2::h3::h4::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h6 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::h2::h3::h4::h5::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    destruct b1 as [ | h7 b1].
    { simpl in H1.
      rewrite H1.
      eexists (a::h1::h2::h3::h4::h5::h6::nil). eexists b2.
      split. reflexivity.
      split. assumption.
      simpl. omega. }
    simpl in H1.
    rewrite H1.
    eexists nil.
    eexists (a::h1::h2::h3::h4::h5::h6::h7::b1 ++ b2).
    split. reflexivity.
    split.
    assert (a :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: b1 ++ b2 =
            (a :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: b1) ++ b2).
    { reflexivity. }
    rewrite H.
    rewrite app_length.
    replace (length (a :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: b1)) with
            (8 + length b1).
    simpl in H3.
    destruct b1.
    + rewrite <- Nat.add_mod_idemp_l.
      simpl.
      apply H2.
      omega.
    + simpl in H3.
      omega.
    + simpl. reflexivity.
    + simpl. omega.
Qed.

Lemma list_segmentize8_r {X:Type}:
  forall (bs:list X),
    exists b1 b2, bs = b1 ++ b2 /\
                  Nat.modulo (List.length b1) 8 = 0 /\
                  List.length b2 < 8.
Proof.
  intros.
  assert (exists b1' b2', (rev bs) = b1' ++ b2' /\
                          Nat.modulo (List.length b2') 8 = 0 /\
                          List.length b1' < 8).
  { eapply list_segmentize8_l. }
  destruct H as [b1' H].
  destruct H as [b2' H].
  destruct H as [H1 [H2 H3]].
  rewrite <- rev_involutive with (l := b1') in H1.
  rewrite <- rev_involutive with (l := b2') in H1.
  rewrite <- rev_app_distr in H1.
  assert (bs = rev b2' ++ rev b1').
  { rewrite <- rev_involutive with (l := bs).
    rewrite H1.
    rewrite rev_involutive.
    reflexivity. }
  exists (rev b2').
  exists (rev b1').
  split.
  - assumption.
  - split.
    rewrite rev_length. assumption.
    rewrite rev_length. assumption.
Qed.

Lemma list_split8_l {X:Type}:
  forall (bs:list X) n
         (HLEN:n = List.length bs)
         (HLEN2:Nat.modulo n 8 = 0)
         (HNEQ:n <> 0),
    exists b1 b2, bs = b1 ++ b2 /\
                  List.length b1 = 8 /\
                  Nat.modulo (List.length b2) 8 = 0.
Proof.
  intros.
  destruct bs as [| h1 bs].
  { simpl in HLEN. omega. }
  destruct bs as [| h2 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h3 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h4 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h5 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h6 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h7 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
  destruct bs as [| h8 bs].
  { simpl in HLEN. rewrite HLEN in HLEN2. inversion HLEN2. }
 exists (h1::h2::h3::h4::h5::h6::h7::h8::nil).
  exists bs.
  split. reflexivity.
  split. reflexivity.
  assert (length (h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: bs) =
          8 + length bs).
  { reflexivity. }
  rewrite H in HLEN.
  rewrite HLEN in HLEN2.
  rewrite <- Nat.add_mod_idemp_l in HLEN2.
  simpl in HLEN2.
  simpl.
  assumption.
  omega.
Qed.



(*******************************************
      Boolean version of List.incl
 *******************************************)

Definition list_inclb {X:Type}
           {eq_dec: forall x y : X, {x = y}+{x <> y}}
           (l1 l2: list X): bool :=
  List.forallb (fun x =>
                  List.existsb (fun y =>
                     match (eq_dec x y) with
                     | left _ => true
                     | right _ => false
                     end) l2) l1.

Lemma list_inclb_refl {X:Type} {eq_dec:forall x y:X, {x = y}+{x<>y}}:
  forall (l:list X), @list_inclb X eq_dec l l = true.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    destruct (eq_dec a a).
    + unfold list_inclb.
      simpl.
      unfold list_inclb in IHl.
      rewrite forallb_forall in *.
      rewrite <- Forall_forall in *.
      apply Forall_impl with (P :=
        (fun x : X => existsb
                        (fun y : X => if eq_dec x y then true else false) l = true)).
      * intros.
        rewrite H. rewrite orb_true_r. reflexivity.
      * assumption.
    + exfalso. auto.
Qed.


(*******************************************
      Numbering each element of a list.
 *******************************************)

Fixpoint _number_list {X:Type} (l:list X) (i:nat): list (nat * X) :=
  match l with
  | nil => nil
  | h::t => (i, h)::(_number_list t (i+1))
  end.

Definition number_list {X:Type} (l:list X): list (nat * X) :=
  _number_list l 0.

Lemma _number_list_len {X:Type}:
  forall (l:list X) i1 i2,
    List.length (_number_list l i1) = List.length (_number_list l i2).
Proof.
  induction l.
  intros. reflexivity.
  intros. simpl. erewrite IHl. reflexivity.
Qed.

Lemma number_list_len {X:Type}:
  forall (l:list X) l'
    (HEQ:l' = number_list l),
    List.length l = List.length l'.
Proof.
  induction l.
  - intros. unfold number_list in HEQ. simpl in HEQ. rewrite HEQ. reflexivity.
  - intros. unfold number_list in HEQ. simpl in HEQ.
    rewrite HEQ. simpl.
    rewrite _number_list_len with (i2 := 0).
    rewrite <- IHl. reflexivity.
    unfold number_list. reflexivity.
Qed.

Lemma _number_list_append {X:Type}:
  forall (l:list X) (h:X) i n
         (HLEN:n = List.length l),
    (_number_list l i) ++ ((n + i, h)::nil) = (_number_list (l ++ (h::nil)) i).
Proof.
  induction l.
  - intros. simpl. rewrite HLEN. reflexivity.
  - simpl. intros.
    destruct n. inversion HLEN.
    inversion HLEN. rewrite <- H0. rewrite <- IHl with (n := n).
    rewrite Nat.add_comm with (n := i) (m := 1). simpl.
    rewrite Nat.add_succ_r.
    reflexivity.
    assumption.
Qed.

Lemma _number_list_nth_fst {X:Type}:
  forall (l:list X) n def i,
    fst (List.nth n (_number_list l i) (n + i, def)) = n + i.
Proof.
  induction l.
  - intros. simpl. destruct n. reflexivity. reflexivity.
  - intros. simpl. destruct n. reflexivity.
    simpl.
    rewrite <- Nat.add_succ_r with (n := n) (m := i).
    rewrite Nat.add_comm with (n := i) (m := 1).
    simpl.
    rewrite IHl with (n := n) (def := def) (i := S i).
    reflexivity.
Qed.

Lemma _number_list_nth_snd {X:Type}:
  forall (l:list X) n m def i,
    snd (List.nth n (_number_list l i) (m, def)) = List.nth n l def.
Proof.
  induction l.
  - intros. simpl. destruct n; reflexivity.
  - simpl. destruct n. intros. reflexivity.
    intros. simpl.
    rewrite IHl. reflexivity.
Qed.

Theorem list_number_nth {X:Type}:
  forall (l:list X) n def,
    List.nth n (number_list l) (n, def) = (n, List.nth n l def).
Proof.
  intros.
  remember (List.nth n (number_list l) (n, def)) as res.
  destruct res.
  assert (n0 = fst (nth n (number_list l) (n, def))).
  { rewrite <- Heqres. reflexivity. }
  assert (x = snd (nth n (number_list l) (n, def))).
  { rewrite <- Heqres. reflexivity. }
  unfold number_list in H, H0.
  replace (n, def) with (n+0, def) in H, H0.
  rewrite _number_list_nth_fst in H.
  rewrite _number_list_nth_snd in H0.
  rewrite Nat.add_0_r in H.
  rewrite H, H0. reflexivity.
  rewrite Nat.add_0_r. reflexivity.
Qed.


(**************************************************
   Checking all two adjacent elements in a list.
 **************************************************)

Fixpoint forall_adj {X:Type} (f:X -> X -> bool) (l:list X) :=
  match l with
  | nil => true
  | h::t =>
    match t with
    | nil => true
    | h2::t' => (f h h2) && (forall_adj f t)
    end                     
  end.


(*******************************************
      Subsequence of a list.
 *******************************************)

Inductive lsubseq {X:Type}: list X -> list X -> Prop :=
| ss_nil: forall (l:list X), lsubseq l nil
| ss_cons: forall (x:X) (l1 l2:list X) (H:lsubseq l1 l2),
    lsubseq (x::l1) (x::l2)
| ss_elon: forall (x:X) (l1 l2:list X) (H:lsubseq l1 l2),
    lsubseq (x::l1) l2.

Lemma lsubseq_refl: forall {X:Type} (l:list X), lsubseq l l.
Proof.
  intros.
  induction l. constructor. constructor. assumption.
Qed.

Lemma lsubseq_inv:
  forall {X:Type} (l1 l2:list X) (x:X)
         (H:lsubseq l1 (x::l2)),
    lsubseq l1 l2.
Proof.
  intros.
  induction l1.
  - inversion H.
  - inversion H.
    + apply ss_elon. assumption.
    + apply ss_elon. apply IHl1.
      assumption.
Qed.

Lemma lsubseq_trans:
  forall {X:Type} (l1 l2 l3:list X)
         (H1:lsubseq l1 l2)
         (H2:lsubseq l2 l3),
    lsubseq l1 l3.
Proof.
  intros.
  generalize dependent l3.
  induction H1 as [| x l1' l2' | x l1' l2'].
  - intros. inversion H2. constructor.
  - intros.
    inversion H2 as [| y l2'' l3' | y l2'' l3'].
    + constructor.
    + constructor. apply IHlsubseq. assumption.
    + apply ss_elon.
      apply IHlsubseq.
      assumption.
  - intros.
    apply ss_elon.
    apply IHlsubseq.
    assumption.
Qed.    

Lemma lsubseq_In:
  forall {X:Type} (l l':list X) (x:X)
         (HIN:List.In x l')
         (HLSS:lsubseq l l'),
    List.In x l.
Proof.
  intros.
  induction HLSS.
  - simpl in HIN. inversion HIN.
  - simpl in HIN.
    destruct HIN.
    + rewrite H. simpl. auto.
    + simpl. right. apply IHHLSS. assumption.
  - simpl. right. apply IHHLSS. assumption.
Qed.


(* Lemma: if length if output is larger than input,
   lsubseq does not hold. *)
Lemma lsubseq_exceed:
  forall {X:Type} (l l':list X)
         (HLEN:List.length l' > List.length l),
    ~ lsubseq l l'.
Proof.
  intros.
  intros H.
  induction H.
  - simpl in HLEN.
    destruct (length l).
    inversion HLEN. inversion HLEN.
  - simpl in HLEN.
    apply Gt.gt_S_n in HLEN.
    apply IHlsubseq. assumption.
  - simpl in HLEN.
    apply IHlsubseq.
    apply Gt.gt_trans with (m := S (length l1)).
    assumption.
    constructor.
Qed.

(* Lemma: if length of input is same as output,
   the input equals the output. *)
Lemma lsubseq_full:
  forall {X:Type} (l l':list X)
         (H:lsubseq l l')
         (HLEN:List.length l = List.length l'),
    l = l'.
Proof.
  intros X l.
  induction l.
  - intros.
    simpl in HLEN. symmetry in HLEN. rewrite length_zero_iff_nil in HLEN.
    congruence.
  - intros.
    destruct l'.
    simpl in HLEN. inversion HLEN.
    simpl in HLEN. inversion HLEN.
    inversion H.
    + rewrite IHl with (l' := l').
      reflexivity.
      assumption.
      assumption.
    + exfalso.
      eapply lsubseq_exceed.
      assert (length (x::l') > length l').
      { simpl. constructor. }
      apply H5.
      rewrite IHl with (l' := l') in H4.
      assumption.
      eapply lsubseq_inv. eassumption.
      assumption.
Qed.

Lemma lsubseq_filter: forall {X:Type} (l:list X) f,
    lsubseq l (List.filter f l).
Proof.
  intros.
  induction l. constructor. simpl.
  destruct (f a) eqn:H. constructor. assumption.
  constructor. assumption.
Qed.

Lemma lsubseq_append: forall {X:Type} (l1 l2 l3 l4:list X)
                             (H1:lsubseq l1 l2)
                             (H2:lsubseq l3 l4),
    lsubseq (l1++l3) (l2++l4).
Proof.
  intros.
  induction H1.
  - simpl.
    induction l. assumption.
    simpl. constructor. assumption.
  - simpl. constructor. assumption.
  - simpl. constructor. assumption.
Qed.

Lemma lsubseq_append2: forall {X:Type} (l0 l1 l2:list X)
                             (H1:lsubseq l1 l2),
    lsubseq (l0++l1) (l2).
Proof.
  intros.
  induction l0.
  - simpl. assumption.
  - simpl. constructor. assumption.
Qed.

Lemma lsubseq_combine:
  forall {X Y:Type} (a1 a2:list X) (b1 b2:list Y)
         (HLEN1:List.length a1 = List.length b1)
         (HLEN2:List.length a2 = List.length b2)
         (HSS:lsubseq (List.combine a1 b1) (List.combine a2 b2)),
    lsubseq a1 a2 /\ lsubseq b1 b2.
Proof.
  intros.
  remember (combine a1 b1) as c1.
  remember (combine a2 b2) as c2.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent b1.
  generalize dependent b2.
  induction HSS.
  - intros.
    assert (a2 = nil /\ b2 = nil).
    { apply combine_length_nil.
      assumption. congruence. }
    destruct H. rewrite H in *. rewrite H0 in *.
    split; constructor.
  - intros.
    symmetry in Heqc1, Heqc2.
    assert (H1 := combine_length_some a1 b1 x l1 HLEN1 Heqc1).
    assert (H2 := combine_length_some a2 b2 x l2 HLEN2 Heqc2).
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    rewrite H11, H12, H21, H22.
    assert (HH:lsubseq (fst (split l1)) (fst (split l2)) /\
               lsubseq (snd (split l1)) (snd (split l2)) ->
               lsubseq (fst x :: fst (split l1)) (fst x :: fst (split l2)) /\
               lsubseq (snd x :: snd (split l1)) (snd x :: snd (split l2))).
    { intros.
      destruct H.
      split; constructor; assumption.
    }
    apply HH. clear HH.
    apply IHHSS.
    + rewrite H21 in HLEN2. rewrite H22 in HLEN2.
      simpl in HLEN2. apply Nat.succ_inj. assumption.
    + rewrite H21, H22 in Heqc2.
      simpl in Heqc2. inversion Heqc2. rewrite H1. congruence.
    + rewrite H11 in HLEN1. rewrite H12 in HLEN1.
      simpl in HLEN1. congruence.
    + rewrite H11, H12 in Heqc1.
      simpl in Heqc1. inversion Heqc1. rewrite H1. congruence.
  - intros.
    symmetry in Heqc1.
    assert (H1 := combine_length_some a1 b1 x l1 HLEN1 Heqc1).
    assert (HH:lsubseq (fst (split l1)) a2 /\
               lsubseq (snd (split l1)) b2 ->
               lsubseq (fst x :: fst (split l1)) a2 /\
               lsubseq (snd x :: snd (split l1)) b2).
    { intros.
      destruct H.
      split; constructor; assumption.
    }
    destruct H1 as [H11 H12].
    rewrite H11, H12.
    apply HH. clear HH.
    apply IHHSS.
    + assumption.
    + congruence.
    + rewrite H11, H12 in HLEN1.
      simpl in HLEN1. apply Nat.succ_inj. assumption.
    + apply combine_fst_snd_split.
Qed.

Lemma lsubseq_len:
  forall {X:Type} (l l':list X)
         (HLSS:lsubseq l l'),
    List.length l' <= List.length l.
Proof.
  intros.
  induction HLSS.
  - simpl.
    apply Nat.le_0_l.
  - simpl.
    apply le_n_S. assumption.
  - simpl. constructor. assumption.
Qed.

Lemma lsubseq_split_snd:
  forall {X Y:Type} (l1 l2:list (X * Y))
         (HLSS:lsubseq l1 l2),
    lsubseq (snd (List.split l1)) (snd (List.split l2)).
Proof.
  intros.
  induction HLSS.
  - simpl. constructor.
  - simpl. destruct x.
    remember (split l1) as tmp.
    destruct tmp as [a1 b1].
    remember (split l2) as tmp.
    destruct tmp as [a2 b2].
    simpl in IHHLSS.
    simpl. constructor. assumption.
  - simpl. destruct x.
    remember (split l1) as tmp.
    destruct tmp as [a1 b1].
    simpl in *. constructor. assumption.
Qed.

Lemma lsubseq_forallb: forall {X:Type} (l l':list X) f
                             (H:List.forallb f l = true)
                             (HLSS:lsubseq l l'),
    List.forallb f l' = true.
Proof.
  intros.
  induction HLSS.
  - constructor.
  - simpl in *.
    rewrite andb_true_iff in *.
    destruct H.
    split. assumption. apply IHHLSS. assumption.
  - simpl in H. rewrite andb_true_iff in H.
    destruct H. apply IHHLSS. assumption.
Qed.

Lemma lsubseq_NotIn {X:Type}:
  forall (l l':list X) a
         (HLSS:lsubseq l l')
         (HNIN:~List.In a l),
    ~List.In a l'.
Proof.
  intros. intros H.
  apply HNIN.
  eapply lsubseq_In. eassumption. assumption.
Qed.

Lemma lsubseq_NoDup {X:Type}:
  forall (l l':list X)
         (HLSS:lsubseq l l')
         (HNDP:NoDup l),
    NoDup l'.
Proof.
  intros.
  induction HLSS.
  - constructor.
  - inversion HNDP.
    apply IHHLSS in H2.
    apply NoDup_cons.
    eapply lsubseq_NotIn.
    eassumption.
    assumption. assumption.
  - inversion HNDP.
    apply IHHLSS. assumption.
Qed.

Lemma lsubseq_map {X Y:Type}:
  forall (l l':list X) (lm lm':list Y) (f:X -> Y)
         (HLSS:lsubseq l l')
         (HLM:lm = List.map f l)
         (HLM':lm' = List.map f l'),
    lsubseq lm lm'.
Proof.
  intros.
  generalize dependent lm.
  generalize dependent lm'.
  induction HLSS.
  - intros. simpl in HLM'. rewrite HLM'.
    constructor.
  - intros. destruct lm. inversion HLM.
    destruct lm'. inversion HLM'.
    simpl in HLM. inversion HLM.
    simpl in HLM'. inversion HLM'.
    constructor.
    apply IHHLSS.
    reflexivity. reflexivity.
  - intros. destruct lm. inversion HLM.
    simpl in HLM. inversion HLM.
    constructor.
    apply IHHLSS.
    assumption. reflexivity.
Qed.

Lemma notIn_filter_nat:
  forall (l:list nat) (key:nat)
         (HNOTIN:~List.In key l),
   filter (fun x => x =? key) l = nil.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in HNOTIN.
    apply Decidable.not_or in HNOTIN.
    destruct HNOTIN.
    apply IHl in H0.
    simpl. rewrite H0.
    destruct (a =? key) eqn:HD.
    + apply beq_nat_true in HD. omega.
    + reflexivity.
Qed.

(*******************************************
   Finding a value by key (which is nat)
   & Updateing a value with key
 *******************************************)

Definition list_find_key {X:Type} (l:list (nat * X)) (key:nat)
:list (nat * X) :=
  List.filter (fun x => fst x =? key) l.

Definition list_set {X:Type} (l:list (nat * X)) (key:nat) (v:X)
:list (nat * X) :=
  List.map (fun x => if fst x =? key then (key, v) else x) l.

Definition list_keys {X:Type} (l:list (nat * X))
:list nat :=
  List.map fst l.

Lemma list_keys_In {X:Type}:
  forall (l:list (nat * X)) key val
         (HIN:List.In (key, val) l),
    List.In key (list_keys l).
Proof.
  intros.
  generalize dependent key.
  generalize dependent val.
  induction l.
  - intros. inversion HIN.
  - intros. inversion HIN. rewrite H.
    simpl. left. reflexivity.
    simpl. right. eapply IHl. eassumption.
Qed.

Lemma decompose_by_key {X:Type}:
  forall (l:list (nat * X)) key
         (HNODUP:NoDup (list_keys l))
         (HIN:List.In key (list_keys l)),
    exists l1 l2 v, l = l1 ++ (key, v)::l2 /\
                    ~List.In key (list_keys l1) /\
                    ~List.In key (list_keys l2).
Proof.
  intros.
  induction l.
  - inversion HIN.
  - destruct a as [newkey newval].
    simpl in HNODUP.
    simpl in HIN.
    destruct HIN as [HIN | HIN].
    + exists nil.
      exists l.
      exists newval.
      simpl.
      split. congruence.
      split. intros HH; inversion HH.
      inversion HNODUP. rewrite HIN in H1. assumption.
    + inversion HNODUP.
      apply IHl in H2.
      destruct H2 as [l1 [l2 [v0 [HH1 [HH2 HH]]]]].
      exists ((newkey, newval)::l1).
      exists l2.
      exists v0.
      rewrite HH1.
      split. reflexivity.
      split. simpl.
      intros H'. destruct H' as [H' | H'].
      rewrite H' in H1. apply H1 in HIN. omega.
      apply HH2 in H'. omega.
      assumption.
      assumption.
Qed.

Lemma list_set_keys_eq {X:Type}:
  forall (l l':list (nat * X)) key x
         (HMAP:l' = list_set l key x),
    list_keys l' = list_keys l.
Proof.
  intros.
  generalize dependent l'.
  induction l.
  - simpl. intros. rewrite HMAP. reflexivity.
  - simpl. intros.
    destruct (fst a =? key) eqn:Heq.
    + destruct l'. inversion HMAP.
      inversion HMAP.
      rewrite Nat.eqb_eq in Heq.
      rewrite Heq. simpl. erewrite IHl. reflexivity. reflexivity.
    + destruct l'. inversion HMAP.
      inversion HMAP. simpl. erewrite IHl. reflexivity. reflexivity.
Qed.

Lemma list_set_eq {X:Type}:
  forall (l:list (nat * X)) (key:nat) (val:X)
         (HIN:List.In (key, val) l)
         (HNODUP:List.NoDup (List.map fst l)),
  list_set l key val = l.
Proof.
  intros.
  unfold list_set.
  generalize dependent key.
  generalize dependent val.
  induction l.
  - simpl. intros. inversion HIN.
  - simpl. intros.
    simpl in HNODUP.
    inversion HNODUP.
    destruct HIN as [HIN | HIN].
    + rewrite HIN in H1. simpl in H1.
      rewrite HIN. simpl. rewrite Nat.eqb_refl.
      assert (HNE:~ List.Exists (fun x => x = key) (map fst l)).
      { intros HX.
        apply H1.
        rewrite Exists_exists in HX.
        destruct HX as [key' HX].
        destruct HX as [HX1 HX2].
        rewrite HX2 in HX1. assumption. }
      rewrite <- Forall_Exists_neg in HNE.
      clear H2 H1 IHl HNODUP H0.
      induction l.
      * reflexivity.
      * simpl in HNE.
        inversion HNE.
        apply IHl in H3. simpl.
        rewrite <- Nat.eqb_neq in H2.
        rewrite H2.
        inversion H3.
        rewrite H5. rewrite H5. reflexivity.
    + assert (fst a <> key).
      {
        apply in_split_l in HIN.
        simpl in HIN.
        rewrite map_fst_split in H1.
        eapply In_notIn_neq.
        eassumption. assumption.
      }
      rewrite <- Nat.eqb_neq in H3.
      rewrite H3.
      rewrite IHl. reflexivity. assumption. assumption.
Qed.

Lemma list_set_NoDup_key {X:Type}:
  forall (l l':list (nat * X)) key v
         (HNODUP:NoDup (list_keys l))
         (HSET:l' = list_set l key v),
    NoDup (list_keys l').
Proof.
  intros.
  erewrite list_set_keys_eq.
  eassumption. eassumption.
Qed.

Lemma list_set_In {X:Type}:
  forall (l l':list (nat * X)) key v
         (HKEYIN:List.In key (list_keys l))
         (HSET:l' = list_set l key v),
    List.In (key, v) l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try (inversion HKEYIN; fail).
  intros.
  simpl in HSET.
  destruct (fst a =? key) eqn:HEQ.
  - rewrite HSET. auto. simpl. auto.
  - simpl in HKEYIN.
    destruct HKEYIN as [HKEYIN | HKEYIN].
    + rewrite Nat.eqb_neq in HEQ. omega.
    + rewrite HSET. simpl. right.
      apply IHl. assumption. reflexivity.
Qed.

Lemma list_set_In_key {X:Type}:
  forall (l l':list (nat * X)) key v
         (HNODUP:List.In key (list_keys l))
         (HSET:l' = list_set l key v),
    List.In key (list_keys l').
Proof.
  intros.
  erewrite list_set_keys_eq.
  eassumption.
  eassumption.
Qed.

Lemma list_set_notIn_key {X:Type}:
  forall (l:list (nat * X)) key v
         (HNODUP: ~List.In key (list_keys l)),
    l = list_set l key v.
Proof.
  intros.
  induction l.
  - intros. reflexivity.
  - intros. simpl.
    simpl in HNODUP.
    destruct (fst a =? key) eqn:Heq.
    + rewrite Nat.eqb_eq in Heq. rewrite Heq in HNODUP. omega.
    + rewrite Nat.eqb_neq in Heq.
      rewrite <- IHl.
      reflexivity.
      apply Decidable.not_or in HNODUP. destruct HNODUP. assumption.
Qed.

Lemma list_set_NoDup_In_unique {X:Type}:
  forall (l:list (nat * X)) (key:nat) (x x0:X)
         (HIN:List.In (key, x0) (list_set l key x))
         (HNODUP:List.NoDup (list_keys l)),
    x0 = x.
Proof.
  intros.
  unfold list_keys in HNODUP.
  remember (map fst l) as l'.
  generalize dependent l.
  induction HNODUP.
  - simpl. intros. destruct l; try (inversion Heql'; fail). simpl in HIN.
    inversion HIN.
  - intros.
    destruct l0 as [ | h0 t0].
    + inversion Heql'.
    + destruct h0 as [key0 v0].
      simpl in Heql'.
      inversion Heql'.
      simpl in HIN.
      destruct HIN.
      * destruct (key0 =? key) eqn:Hkey0.
        inversion H0. reflexivity.
        inversion H0. rewrite Nat.eqb_neq in Hkey0. omega.
      * apply IHHNODUP with (l0 := t0). assumption.
        assumption.
Qed.

Lemma list_keys_In_False {X:Type}:
  forall (l:list (nat * X)) key x
         (HNOTIN:~ In key (list_keys l))
         (HIN:In (key, x) l),
    False.
Proof.
  intros.
  induction l.
  - inversion HIN.
  - simpl in HIN. simpl in HNOTIN.
    destruct HIN as [HIN | HIN].
    rewrite HIN in HNOTIN.
    apply HNOTIN. left. reflexivity.
    apply Decidable.not_or in HNOTIN.
    destruct HNOTIN.
    apply IHl in H0. assumption. assumption.
Qed.


Lemma list_set_decompose {X:Type}:
  forall (l l':list (nat * X)) key v
         (HNODUP:NoDup (list_keys l))
         (HIN:List.In key (list_keys l))
         (HSET:l' = list_set l key v),
    exists l1 l2 v0,
       (l = l1 ++ (key, v0)::l2 /\
        l' = l1 ++ (key, v)::l2 /\
       ~List.In key (list_keys l1) /\
       ~List.In key (list_keys l2)).
Proof.
  intros.
  assert (NoDup (list_keys l')).
  { eapply list_set_NoDup_key; eassumption. }
  assert (List.In key (list_keys l')).
  { eapply list_set_In_key; eassumption. }
  assert (HD := decompose_by_key l key HNODUP HIN).
  assert (HD':= decompose_by_key l' key H H0).
  destruct HD' as [l1' [l2' [v0' [HD'1 [HD'2 HD'3]]]]].
  destruct HD as [l1 [l2 [v0 [HD1 [HD2 HD3]]]]].
  assert (H12: l1 = l1' /\ l2 = l2' /\ (key, v0') = (key, v)).
  { rewrite HD'1, HD1 in HSET.
    unfold list_set in HSET.
    rewrite map_app in HSET.
    simpl in HSET. rewrite Nat.eqb_refl in HSET.
    assert (H11:l1 = list_set l1 key v).
    { apply list_set_notIn_key. assumption. }
    assert (H12:l2 = list_set l2 key v).
    { apply list_set_notIn_key. assumption. }
    unfold list_set in H11, H12.
    rewrite <- H11, <- H12 in HSET.
    apply app_equal with (x := (key, v)) (x' := (key, v0')).
    { intros H00.
      eapply list_keys_In_False. eapply HD2. eassumption. }
    { intros H00.
      eapply list_keys_In_False. eapply HD'2. eassumption. }
    assumption.
  }
  destruct H12 as [H1 [H2 HITM]].
  inversion HITM. rewrite H4 in *. clear H4 HITM.
  exists l1', l2', v0.
  split.
  - congruence.
  - split.
    assumption.
    split; assumption.
Qed.

Lemma list_find_key_NoDup {X:Type}:
  forall (l res:list (nat * X)) (key:nat)
         (HNODUP:NoDup (list_keys l))
         (HRES:res = list_find_key l key),
    List.length res < 2.
Proof.
  intros.
  remember (split l) as ls.
  destruct ls as [lsk lsv].
  unfold list_keys in HNODUP.
  rewrite map_fst_split in HNODUP.
  rewrite <- Heqls in HNODUP. simpl in HNODUP.
  assert (List.map fst (List.filter (fun x => fst x =? key) l) =
          List.filter (fun x => x =? key) lsk).
  {
    clear HNODUP.
    clear HRES.
    generalize dependent lsk.
    generalize dependent lsv.
    induction l.
    - intros. simpl in Heqls. inversion Heqls.
      reflexivity.
    - intros. destruct a. simpl in Heqls.
      remember (split l) as l'.
      destruct l'.
      inversion Heqls. destruct lsk. inversion H0.
      destruct lsv. inversion H1.
      simpl.
      destruct (n =? key) eqn:HKEY.
      + simpl. erewrite IHl. reflexivity. reflexivity.
      + erewrite IHl. reflexivity. reflexivity.
  }
  unfold list_find_key in HRES.
  rewrite <- HRES in H.
  rewrite map_fst_split in H.
  remember (split res) as ress.
  destruct ress as [resk resv].
  simpl in H.
  rewrite <- split_length_l.
  rewrite <- Heqress. simpl.
  clear HRES Heqls l Heqress.
  (* assert (NoDup resk).
  { apply lsubseq_NoDup with (l := lsk).
    rewrite H. apply lsubseq_filter. assumption. } *)
  induction HNODUP as [ | lskh lsht IH].
  - simpl in H. rewrite H. simpl. omega.
  - simpl in H.
    destruct (lskh =? key) eqn: Hflag.
    + apply beq_nat_true in Hflag.
      rewrite <- Hflag in *.
      apply notIn_filter_nat in IH.
      rewrite IH in H. rewrite H. simpl. omega.
    + apply IHHNODUP. assumption.
Qed.

Lemma list_find_key_In {X:Type}:
  forall (l:list (nat * X)) key val
         (HIN:List.In (key,val) l),
    List.In (key,val) (list_find_key l key).
Proof.
  intros.
  unfold list_find_key.
  apply filter_In.
  split. assumption. simpl. rewrite PeanoNat.Nat.eqb_refl. auto.
Qed.

Lemma list_set_In_not_In {X:Type}:
  forall (l:list (nat * X)) (key key0:nat) (x x0:X)
         (HIN:List.In (key0, x0) (list_set l key x))
         (HNEQ:key0 <> key),
    List.In (key0, x0) l.
Proof.
  intros.
  induction l.
  - simpl in HIN. inversion HIN.
  - simpl in HIN.
    destruct HIN.
    + destruct a. simpl in H.
      destruct (n =? key) eqn:Heq.
      inversion H. omega.
      rewrite Nat.eqb_neq in Heq. inversion H.
      simpl. auto.
    + apply IHl in H. simpl. right. assumption.
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

(* Returns a list of ranges which include i. *)
Definition disjoint_include (rs:list (nat * nat)) (i:nat): list (nat*nat) :=
  List.filter (in_range i) rs.

Definition disjoint_include2 {X:Type} (rs:list (nat * nat)) (data:list X) (i:nat)
: list (nat*nat) * list X :=
  List.split
    (List.filter (fun x => in_range i x.(fst))
                 (List.combine rs data)).

Definition no_empty_range (rs:list (nat * nat)): bool :=
  List.forallb (fun t => Nat.ltb 0 t.(snd)) rs.



(* Lemma: two ranges with same begin index & non-zero length overlaps. *)
Lemma disjoint_same:
  forall b1 b2 l1 l2 (HL1:0 < l1) (HL2: 0 < l2) (HEQ:b1 = b2),
    disjoint_range (b1, l1) (b2, l2) = false.
Proof.
  intros.
  unfold disjoint_range.
  rewrite orb_false_iff.
  repeat (rewrite Nat.leb_nle).
  split; rewrite HEQ; apply Gt.gt_not_le; apply Nat.lt_add_pos_r; auto.
Qed.

(* Same as disjoint_same, but with same end index. *)
Lemma disjoint_same2:
  forall b1 b2 l1 l2 (HL1:0 < l1) (HL2:0 < l2) (HEQ:b1 + l1 = b2 + l2),
    disjoint_range (b1, l1) (b2, l2) = false.
Proof.
  intros.
  unfold disjoint_range.
  rewrite orb_false_iff.
  repeat (rewrite Nat.leb_nle).
  split.
  - rewrite HEQ; apply Gt.gt_not_le; apply Nat.lt_add_pos_r; auto.
  - rewrite <- HEQ; apply Gt.gt_not_le; apply Nat.lt_add_pos_r; auto.
Qed.

(* Lemma: no_empty_range still holds for appended lists *)
Lemma no_empty_range_append:
  forall l1 l2 (H1:no_empty_range l1 = true) (H2:no_empty_range l2 = true),
    no_empty_range (l1++l2) = true.
Proof.
  intros.
  induction l1.
  - simpl. assumption.
  - simpl in H1.
    simpl. rewrite andb_true_iff in *.
    destruct H1.
    split. assumption. apply IHl1. assumption.
Qed.

(* Lemma: no_empty_range holds for subsequences *)
Lemma no_empty_range_lsubseq:
  forall l1 l2 (H1:no_empty_range l1 = true) (HLSS:lsubseq l1 l2),
    no_empty_range l2 = true.
Proof.
  intros.
  induction HLSS. reflexivity.
  simpl. simpl in H1. rewrite andb_true_iff in *.
  destruct H1. split. assumption. apply IHHLSS. assumption.
  apply IHHLSS. simpl in H1. rewrite andb_true_iff in *.
  destruct H1. assumption.
Qed.

(* Lemma: no_empty_range holds for concatenated lists *)
Lemma no_empty_range_concat:
  forall (ll:list (list (nat * nat)))
         (HALL:forall l (HIN:List.In l ll), no_empty_range l = true),
    no_empty_range (List.concat ll) = true.
Proof.
  intros.
  induction ll.
  - reflexivity.
  - simpl. apply no_empty_range_append.
    apply HALL. constructor. reflexivity.
    apply IHll. intros. apply HALL.
    simpl. right. assumption.
Qed.

(* Lemma: the subsequence of disjoint ranges is also disjoint. *)
Lemma disjoint_lsubseq_disjoint:
  forall rs rs'
         (HDISJ:disjoint_ranges rs = true)
         (HLSS:lsubseq rs rs'),
    disjoint_ranges rs' = true.
Proof.
  intros.
  induction HLSS.
  - constructor.
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

Lemma disjoint_ranges_append:
  forall l1 l2 (HDISJ:disjoint_ranges (l1 ++ l2) = true),
    disjoint_ranges l1 = true /\ disjoint_ranges l2 = true.
Proof.
  intros.
  induction l1.
  - simpl in HDISJ.
    split. reflexivity. assumption.
  - simpl in HDISJ.
    rewrite andb_true_iff in HDISJ.
    destruct HDISJ.
    split. simpl. rewrite andb_true_iff. split.
    rewrite forallb_app in H.
    rewrite andb_true_iff in H.
    destruct H. assumption.
    apply IHl1. assumption.
    apply IHl1. assumption.
Qed.

(* Lemma: the result of disjoint_include is subsequence of the input. *)
Lemma disjoint_include_lsubseq:
  forall rs i, lsubseq rs (disjoint_include rs i).
Proof.
  intros. unfold disjoint_include. apply lsubseq_filter.
Qed.

(* Lemma: if lsubseq l1 l2, lsubseq (disjoint_include l1 i)
   (disjoint_include l2 i). *)
Lemma disjoint_include_lsubseq2:
  forall rs1 rs2 i
         (H:lsubseq rs1 rs2),
    lsubseq (disjoint_include rs1 i) (disjoint_include rs2 i).
Proof.
  intros.
  induction H.
  - simpl. constructor.
  - simpl.
    destruct (in_range i x).
    constructor. assumption.
    assumption.
  - simpl.
    destruct (in_range i x).
    constructor. assumption. assumption.
Qed.

(* Lemma: (disjoint_include2 rs data i).fst = disjoint_include rs i *)
Lemma disjoint_include_include2 {X:Type} :
  forall rs (data:list X) i
    (HLEN:List.length rs = List.length data),
    fst (disjoint_include2 rs data i) = disjoint_include rs i.
Proof.
  intros.
  unfold disjoint_include2.
  unfold disjoint_include.
  generalize dependent data.
  induction rs.
  - intros. simpl in HLEN.
    symmetry in HLEN.
    rewrite length_zero_iff_nil in HLEN.
    rewrite HLEN.
    reflexivity.
  - intros.
    destruct data as [ | dh dt].
    + simpl in HLEN. inversion HLEN.
    + simpl in HLEN. inversion HLEN.
      simpl.
      destruct (in_range i a) eqn:HIN.
      * simpl.
        rewrite <- (IHrs dt).
        destruct (split (filter
                           (fun x : nat * nat * X => in_range i (fst x))
                           (combine rs dt))) eqn:H.
        reflexivity. assumption.
      * rewrite <- (IHrs dt).
        reflexivity. assumption.
Qed.

(* Lemma: the result of disjoint_include all satisfies in_range. *)
Lemma disjoint_include_inrange:
  forall rs i rs'
         (HIN:rs' = disjoint_include rs i),
    List.forallb (in_range i) rs' = true.
Proof.
  intros.
  unfold disjoint_include in HIN.
  rewrite HIN.
  apply filter_forallb.
Qed.

(* Lemma: a range that includes i is not filtered out. *)
Lemma disjoint_include_In:
  forall rs i rs' r
         (HDISJ:rs' = disjoint_include rs i)
         (HIN:List.In r rs)
         (HIN':in_range i r = true),
    List.In r rs'.
Proof.
  intros.
  unfold disjoint_include in HDISJ.
  rewrite HDISJ.
  rewrite filter_In.
  split; assumption.
Qed.

(* Lemma: the result of disjoint_include2 is subsequence of the input. *)
Lemma disjoint_include2_lsubseq {X:Type}:
  forall (l l': list X) rs rs' ofs
         (HDISJ: disjoint_include2 rs l ofs = (rs', l')),
    lsubseq (List.combine rs l) (List.combine rs' l').
Proof.
  intros.
  unfold disjoint_include2 in HDISJ.
  remember (combine rs l) as lcomb.
  generalize dependent l.
  generalize dependent l'.
  generalize dependent rs.
  generalize dependent rs'.
  induction lcomb.
  {
    intros.
    simpl in HDISJ.
    inversion HDISJ. constructor.
  }
  {
    intros.
    destruct rs as [|rsh rst];
    destruct l as [|lh lt];
    simpl in Heqlcomb;
    try inversion Heqlcomb.
    clear Heqlcomb.
    rewrite H0 in HDISJ.
    simpl in HDISJ.
    destruct (in_range ofs rsh) eqn:HINR.
    - simpl in HDISJ.
      remember (split (filter (fun x : nat * nat * X => in_range ofs (fst x)) lcomb)) as l0.
      destruct l0 as [rs'' l''].
      inversion HDISJ. 
      simpl.
      apply ss_cons.
      rewrite <- H1.
      eapply IHlcomb. reflexivity. eassumption.
    - apply ss_elon.
      rewrite <- H1.
      eapply IHlcomb.
      assumption. eassumption.
  }
Qed.

(* Lemma: If the inputs of two disjoint_include2 calls have subsequence relation.
   so do their outputs. *)
Lemma disjoint_include2_lsubseq2 {X:Type}:
  forall rs1 rs1' rs2 rs2' (data1 data1' data2 data2':list X) i
         (HLEN1:List.length rs1 = List.length data1)
         (HLEN2:List.length rs2 = List.length data2)
         (H:lsubseq (List.combine rs1 data1) (List.combine rs2 data2))
         (H1: (rs1', data1') = disjoint_include2 rs1 data1 i)
         (H2: (rs2', data2') = disjoint_include2 rs2 data2 i),
    lsubseq (List.combine rs1' data1') (List.combine rs2' data2').
Proof.
  intros.
  generalize dependent rs1'.
  generalize dependent data1'.
  generalize dependent rs2'.
  generalize dependent data2'.
  remember (combine rs1 data1) as rd1.
  remember (combine rs2 data2) as rd2.
  generalize dependent data1.
  generalize dependent rs1.
  generalize dependent data2.
  generalize dependent rs2.
  induction H. (* lsubseq rs1 rs2 *)
  - intros.
    assert (rs2 = nil /\ data2 = nil).
    { apply combine_length_nil. assumption. congruence. }
    destruct H.
    rewrite H in *. rewrite H0 in *.
    intros.
    unfold disjoint_include2 in H2. simpl in H2.
    inversion H2. simpl. constructor.
  - intros.
    assert (rs1 = fst x :: fst (split l1) /\
            data1 = snd x :: snd (split l1)).
    { apply combine_length_some.
      assumption. congruence.
    }
    assert (rs2 = fst x :: fst (split l2) /\
            data2 = snd x :: snd (split l2)).
    { apply combine_length_some.
      assumption. congruence.
    }
    destruct H0 as [HRS1 HDATA1].
    destruct H3 as [HRS2 HDATA2].
    rewrite HRS1, HDATA1 in H1.
    unfold disjoint_include2 in H1.
    simpl in H1.
    rewrite HRS2, HDATA2 in H2.
    unfold disjoint_include2 in H2.
    simpl in H2.
    destruct (in_range i (fst x)) eqn:HINRANGE.
    + rewrite <- combine_fst_snd_split in H1, H2.
      remember (split (filter (fun x : nat * nat * X => in_range i (fst x)) l2)) as res2.
      remember (split (filter (fun x : nat * nat * X => in_range i (fst x)) l1)) as res1.
      destruct res2 as [rs2'' data2''].
      destruct res1 as [rs1'' data1''].
      simpl in H1, H2.
      rewrite <- Heqres2 in H2.
      rewrite <- Heqres1 in H1.
      inversion H1.
      inversion H2.
      simpl.
      apply ss_cons.
      apply IHlsubseq with (rs1 := fst (split l1)) (data1 := snd (split l1))
                           (rs2 := fst (split l2)) (data2 := snd (split l2)).
      * rewrite HRS2 in HLEN2.
        rewrite HDATA2 in HLEN2.
        simpl in HLEN2.
        apply Nat.succ_inj.
        assumption.
      * apply combine_fst_snd_split.
      * rewrite HRS1 in HLEN1. rewrite HDATA1 in HLEN1.
        simpl in HLEN1. apply Nat.succ_inj.
        assumption.
      * apply combine_fst_snd_split.
      * unfold disjoint_include2.
        rewrite <- combine_fst_snd_split.
        assumption.
      * unfold disjoint_include2.
        rewrite <- combine_fst_snd_split.
        assumption.
    + apply IHlsubseq with (rs2 := fst (split l2)) (rs1 := fst (split l1))
                           (data1 := snd (split l1)) (data2 := snd (split l2)).
      * rewrite HDATA2 in HLEN2.
        rewrite HRS2 in HLEN2.
        simpl in HLEN2. apply Nat.succ_inj. assumption.
      * apply combine_fst_snd_split.
      * rewrite HDATA1 in HLEN1. rewrite HRS1 in HLEN1.
        simpl in HLEN1. apply Nat.succ_inj. assumption.
      * apply combine_fst_snd_split.
      * unfold disjoint_include2. assumption.
      * unfold disjoint_include2. assumption.
  - intros.
    assert (rs1 = fst x :: fst (split l1) /\
            data1 = snd x :: snd (split l1)).
    { apply combine_length_some.
      assumption. congruence.
    }
    destruct H0 as [HRS1 HDATA1].
    rewrite HRS1, HDATA1 in H1.
    unfold disjoint_include2 in H1.
    simpl in H1.
    destruct (in_range i (fst x)) eqn:HINRANGE.
    + rewrite <- combine_fst_snd_split in H1.
      remember (split (filter (fun x : nat * nat * X => in_range i (fst x)) l1)) as res1.
      simpl in H1.
      rewrite <- Heqres1 in H1.
      destruct res1 as [rs1'' data1''].
      inversion H1.
      simpl. apply ss_elon.
      apply IHlsubseq with (rs2 := rs2) (rs1 := fst (split l1))
                           (data1 := snd (split l1)) (data2 := data2).
      * assumption.
      * assumption.
      * rewrite split_length_l. rewrite split_length_r.
        reflexivity.
      * apply combine_fst_snd_split.
      * assumption.
      * unfold disjoint_include2.
        rewrite <- combine_fst_snd_split.
        assumption.
    + apply IHlsubseq with (rs2 := rs2) (rs1 := fst (split l1))
                           (data1 := snd (split l1)) (data2 := data2);
        try assumption.
      * rewrite split_length_l, split_length_r.
        reflexivity.
      * apply combine_fst_snd_split.
Qed.


(* If length data = length rs,
   the two list results of disjoint_include2 have
   same length. *)
Lemma disjoint_include2_len {X:Type}:
  forall rs (data:list X) i
         (HLEN:List.length rs = List.length data),
    List.length (fst (disjoint_include2 rs data i)) =
    List.length (snd (disjoint_include2 rs data i)).
Proof.
  intros.
  unfold disjoint_include2.
  rewrite split_length_l.
  rewrite split_length_r.
  reflexivity.
Qed.

Lemma disjoint_include2_In {X:Type}:
  forall rs (data:list X) i res d
         (HLEN:List.length rs = List.length data)
         (HIN:List.In d (List.combine rs data))
         (HIN':in_range i d.(fst) = true)
         (HDISJ:res = disjoint_include2 rs data i),
    List.In d (List.combine res.(fst) res.(snd)).
Proof.
  intros.
  unfold disjoint_include2 in HDISJ.
  remember (filter (fun x => in_range i (fst x)) (combine rs data)) as res'.
  assert (In d res').
  { rewrite Heqres'.
    rewrite filter_In.
    split; assumption. }
  rewrite HDISJ.
  rewrite <- combine_fst_snd_split.
  assumption.
Qed.

(* If ranges can be mapped from data,
   the result of disjoint_include2 can be mapped to. *)
Lemma disjoint_include2_rel {X:Type}:
  forall rs (data:list X) i f
         (HMAP:List.map f data = rs),
    List.map f (snd (disjoint_include2 rs data i)) =
    fst (disjoint_include2 rs data i).
Proof.
  intros.
  remember (disjoint_include2 rs data i) as dj eqn:HDJ. 
  simpl.
  unfold disjoint_include2 in HDJ.
  eapply split_filter_combine_map.
  apply HMAP.
  apply HDJ.
Qed.

(* Given (rs, data) = disjoint_include2 .... , 
   length rs = length data. *)
Lemma disjoint_include2_len2 {X:Type}:
  forall rs (data:list X) i,
    List.length (snd (disjoint_include2 rs data i)) <=
    List.length rs.
Proof.
  intros.
  unfold disjoint_include2.
  rewrite split_length_r.
  apply Nat.le_trans with (List.length (combine rs data)).
  - apply filter_length.
  - rewrite combine_length.
    apply Nat.le_min_l.
Qed.

Lemma disjoint_include2_fold_left_lsubseq {X:Type}:
  forall rs (data:list X) ofss res
         (HRES:res =
               List.fold_left (fun x ofs =>
                                 disjoint_include2 (fst x) (snd x) ofs)
                              ofss (rs, data)),
    lsubseq (List.combine rs data) (List.combine res.(fst) res.(snd)).
Proof.
  intros.
  generalize dependent rs.
  generalize dependent data.
  generalize dependent res.
  induction ofss.
  - intros.
    simpl in HRES. destruct res. inversion HRES.
    simpl. apply lsubseq_refl.
  - intros.
    simpl in HRES.
    remember (disjoint_include2 rs data a) as res'.
    apply lsubseq_trans with (l2 := List.combine (fst res') (snd res')).
    + apply disjoint_include2_lsubseq with (ofs := a).
      destruct res'. rewrite <- Heqres'. reflexivity.
    + apply IHofss.
      destruct res'.
      simpl.
      assumption.
Qed.

Lemma disjoint_include2_fold_left_lsubseq2 {X:Type}:
  forall rs1 rs2 (data1 data2:list X) ofss res1 res2
         (HLEN1:List.length rs1 = List.length data1)
         (HLEN2:List.length rs2 = List.length data2)
         (HRES1:res1 =
               List.fold_left (fun x ofs =>
                                 disjoint_include2 (fst x) (snd x) ofs)
                              ofss (rs1, data1))
         (HRES2:res2 =
               List.fold_left (fun x ofs =>
                                 disjoint_include2 (fst x) (snd x) ofs)
                              ofss (rs2, data2))
         (HLSS:lsubseq (List.combine rs1 data1) (List.combine rs2 data2)),
    lsubseq (List.combine res1.(fst) res1.(snd))
            (List.combine res2.(fst) res2.(snd)).
Proof.
  intros.
  generalize dependent rs1.
  generalize dependent rs2.
  generalize dependent data1.
  generalize dependent data2.
  generalize dependent res1.
  generalize dependent res2.
  induction ofss.
  - simpl. intros. rewrite HRES2, HRES1 in *.
    simpl. apply HLSS.
  - simpl. intros.
    remember (disjoint_include2 rs1 data1 a) as res1'.
    destruct res1' as [rs1' data1'].
    assert(HLEN1':List.length (fst (rs1', data1')) = List.length (snd (rs1', data1'))).
    { rewrite Heqres1'. apply disjoint_include2_len. assumption. }
    simpl in HLEN1'.
    remember (disjoint_include2 rs2 data2 a) as res2'.
    destruct res2' as [rs2' data2'].
    assert(HLEN2':List.length (fst (rs2', data2')) = List.length (snd (rs2', data2'))).
    { rewrite Heqres2'. apply disjoint_include2_len. assumption. }
    simpl in HLEN2'.

    apply IHofss with (rs1:=rs1') (rs2:=rs2') (data1:=data1') (data2:=data2').
    congruence.
    assumption.
    congruence.
    assumption.
    eapply disjoint_include2_lsubseq2 with (rs3 := rs1) (rs4 := rs2).
    eassumption.
    eassumption.
    assumption.
    eassumption.
    assumption.
Qed.

Lemma disjoint_include2_fold_left_len {X:Type}:
  forall rs (data:list X) ofss res
         (HLEN:List.length rs = List.length data)
         (HRES:res =
               List.fold_left (fun x ofs =>
                                 disjoint_include2 (fst x) (snd x) ofs)
                              ofss (rs, data)),
    List.length res.(fst) = List.length res.(snd).
Proof.
  intros.
  generalize dependent rs.
  generalize dependent data.
  generalize dependent res.
  induction ofss.
  - intros. simpl in HRES. destruct res. simpl. inversion HRES. congruence.
  - intros. simpl in HRES.
    remember (disjoint_include2 rs data a) as res'.
    assert (List.length res'.(fst) = List.length res'.(snd)).
    { rewrite Heqres'.
      apply disjoint_include2_len.
      assumption. }
    eapply IHofss.
    + eapply H.
    + destruct res'. simpl. assumption.
Qed.

(* Lemma: If there are two ranges (b1, l1), (b2, l2),
   and they include some natural number i,
   and they are disjoint,
   either (b1 + l1 = b2 /\ i = b2) or (b2 + l2 = b1 /\ i = b1). *)
Lemma inrange2_disjoint:
  forall (b1 l1 b2 l2 i:nat)
         (H1:in_range i (b1, l1) = true)
         (H2:in_range i (b2, l2) = true)
         (HDISJ:disjoint_ranges ((b1,l1)::(b2,l2)::nil) = true),
    (b1 + l1 = b2 /\ i = b2) \/ (b2 + l2 = b1 /\ i = b1).
Proof.
  intros.
  unfold in_range in *.
  unfold disjoint_ranges in HDISJ.
  simpl in HDISJ.
  repeat (rewrite andb_true_r in HDISJ).
  unfold disjoint_range in HDISJ.
  rewrite andb_true_iff in *.
  rewrite orb_true_iff in *.
  repeat (rewrite Nat.leb_le in *).
  simpl in *.
  destruct HDISJ.
  - (* Make i = b1 + l1, from b1 + l1 <= i <= b1 + l1. *)
    assert (i = b1 + l1).
    { apply Nat.le_antisymm. apply H1.
      apply Nat.le_trans with (m := b2). assumption. apply H2. }
    (* Make i = b2, from b2 <= i <= b2. *)
    assert (i = b2).
    { apply Nat.le_antisymm.
      apply Nat.le_trans with (m := b1 + l1). apply H1. assumption.
      apply H2. }
    left. split; congruence.
  - (* Make i = b2 + l2, from b2 + l2 <= i <= b2 + l2. *)
    assert (i = b2 + l2).
    { apply Nat.le_antisymm. apply H2.
      apply Nat.le_trans with (m := b1). assumption. apply H1. }
    assert (i = b1).
    { apply Nat.le_antisymm.
      apply Nat.le_trans with (m := b2 + l2). apply H2. assumption.
      apply H1. }
    right. split; congruence.
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
  destruct r1 as [b1 l1].
  destruct r2 as [b2 l2].
  destruct r3 as [b3 l3].
  (* Prettify HNOEMPTY. *)
  simpl in HNOEMPTY.
  rewrite andb_true_r in HNOEMPTY.
  repeat (rewrite andb_true_iff in HNOEMPTY).
  destruct HNOEMPTY as [HNOEMPTY1 [HNOEMPTY2 HNOEMPTY3]].
  (* Use inrange2_disjoint! *)
  destruct (disjoint_ranges ((b1,l1)::(b2,l2)::nil)) eqn:HDISJ12;
  destruct (disjoint_ranges ((b1,l1)::(b3,l3)::nil)) eqn:HDISJ13.
  - (* Okay, (b1, l1), (b2, l2) are disjoint. *)
    assert (H12:(b1 + l1 = b2 /\ i = b2) \/ (b2 + l2 = b1 /\ i = b1)).
    { apply inrange2_disjoint; assumption. }
    (* (b1, l1), (b3, l3) are also disjoint. *)
    assert (H13:(b1 + l1 = b3 /\ i = b3) \/ (b3 + l3 = b1 /\ i = b1)).
    { apply inrange2_disjoint; assumption. }
    (* Prettify *)
    unfold in_range in *.
    simpl in *.
    repeat (rewrite andb_true_iff in *).
    repeat (rewrite andb_true_r in *).
    repeat (rewrite Nat.leb_le in *).
    repeat (rewrite Nat.ltb_lt in *).
    destruct H12 as [H12 | H12];
    destruct H12 as [H12 H12'];
    destruct H13 as [H13 | H13];
    destruct H13 as [H13 H13'].
    + assert (disjoint_range (b2, l2) (b3, l3) = false).
      { apply disjoint_same. assumption. assumption. congruence. }
      rewrite H. rewrite andb_false_r. auto.
    + assert (disjoint_range (b1, l1) (b2, l2) = false).
      { apply disjoint_same. assumption. assumption. congruence. }
      rewrite H. reflexivity.
    + assert (disjoint_range (b1, l1) (b3, l3) = false).
      { apply disjoint_same. assumption. assumption. congruence. }
      rewrite H. rewrite andb_false_r. auto.
    + assert (disjoint_range (b2, l2) (b3, l3) = false).
      { apply disjoint_same2. assumption. assumption. congruence. }
      rewrite H. rewrite andb_false_r. auto.
  - (* No, (b1, l1), (b3, l3) overlap. *)
    simpl in *.
    repeat (rewrite andb_true_r in *).
    rewrite HDISJ13. rewrite andb_false_r. auto.
  - (* No, (b1, l1), (b2, l2) overlap. *)
    simpl in *.
    repeat (rewrite andb_true_r in *).
    rewrite HDISJ12. auto.
  - (* (b1, l1) - (b3, l3) overlap, and (b1, l1) - (b2, l2) overlap too. *)
    simpl in *.
    repeat (rewrite andb_true_r in *).
    rewrite HDISJ12. auto.
Qed.

(* Theorem: If ranges are disjoint, there are at most 2 ranges
   which have number i in-range. *)
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
    destruct HNOZERO as [HNOZERO0 HNOZERO].
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
          assert (HDISJ0:forallb (fun r2 : nat * nat => disjoint_range (beg, len) r2)
                          ((beg1,len1)::(beg2,len2)::nil) = true).
          {
            apply lsubseq_forallb with (l := rs).
            assumption.
            rewrite H1.
            apply disjoint_include_lsubseq.
          }
          assert (HDISJ12: disjoint_ranges ((beg1, len1)::(beg2, len2)::nil) = true).
          {
            apply disjoint_lsubseq_disjoint with (rs := rs).
            assumption.
            rewrite H1.
            apply disjoint_include_lsubseq.
          }
          (* Okay, we got (beg, len) (beg1, len1) disjoint,
             (beg, len) (beg2, len2) disjoint. *)
          simpl in HDISJ0.
          rewrite andb_true_r in HDISJ0.
          rewrite andb_true_iff in HDISJ0.
          destruct HDISJ0 as [HDISJ01 HDISJ02].
          simpl in HDISJ12.
          repeat (rewrite andb_true_r in HDISJ12).
          (* Make in_range predicates. *)
          assert (HIN12: List.forallb (in_range i)
                                      ((beg1,len1)::(beg2,len2)::nil) = true).
          {
            rewrite H1.
            unfold disjoint_include.
            apply filter_forallb.
          }
          simpl in HIN12.
          repeat (rewrite andb_true_iff in HIN12).
          destruct HIN12 as [HIN1 [HIN2 _]].
          (* Non-zero-size range. *)
          assert (HNOZERO12: no_empty_range ((beg1,len1)::(beg2,len2)::nil) = true).
          {
            unfold no_empty_range.
            rewrite H1.
            apply lsubseq_forallb with (l := rs).
            apply HNOZERO. apply disjoint_include_lsubseq.
          }
          simpl in HNOZERO12.
          repeat (rewrite andb_true_iff in HNOZERO12).
          destruct HNOZERO12 as [HNOZERO1 [HNOZERO2 _]].
          (* Now, the main theorem. *)
          assert (HMAIN: disjoint_ranges
                           ((beg, len)::(beg1, len1)::(beg2, len2)::nil) = false).
          {
            apply inrange3_never_disjoint with (i := i).
            assumption. assumption. assumption.
            simpl. simpl in HNOZERO0.
            rewrite HNOZERO0. rewrite HNOZERO1. rewrite HNOZERO2.
            reflexivity.
          }
          (* Make False *)
          simpl in HMAIN.
          rewrite HDISJ01 in HMAIN.
          rewrite HDISJ02 in HMAIN.
          rewrite HDISJ12 in HMAIN.
          simpl in HMAIN.
          inversion HMAIN.
        }
        { (* disjoint_include already returned more than 2 ranges.
             This is impossible. *)
          simpl in H.
          exfalso.
          apply (Lt.le_not_lt 3 (3 + length rs'tttt)).
          repeat (apply le_n_S).
          apply le_0_n.
          apply H.
        }
   + (* No new range fit *)
     apply IHrs.
     assumption.
     assumption.
     assumption.
Qed.

(* If (b1, l1) (b2, l2) are disjoint,
   and i != b1 /\ i != b2,
   then i cannot belong to both ranges. *) 
Lemma inrange2_false:
  forall b1 l1 b2 l2 i
         (HDISJ:disjoint_ranges ((b1, l1)::(b2, l2)::nil) = true)
         (HNOTBEG:~(i = b1 \/ i = b2)),
    in_range i (b1,l1) && in_range i (b2, l2) = false.
Proof.
  intros.
  simpl in HDISJ.
  repeat (rewrite andb_true_r in HDISJ).
  unfold disjoint_range in HDISJ.
  rewrite orb_true_iff in HDISJ.
  repeat (rewrite Nat.leb_le in HDISJ).
  remember (in_range i (b1, l1)) as v1.
  remember (in_range i (b2, l2)) as v2.
  unfold in_range in *.
  simpl in *.
  destruct v1; destruct v2; try reflexivity.
  {
    symmetry in Heqv1.
    symmetry in Heqv2.
    rewrite andb_true_iff in *.
    repeat (rewrite Nat.leb_le in *).
    destruct HDISJ.
    - assert (i = b2).
      {
        apply Nat.le_antisymm.
        - apply Nat.le_trans with (m := b1 + l1).
          apply Heqv1. apply H.
        - apply Heqv2.
      }
      exfalso.
      apply HNOTBEG. right. assumption.
    - assert (i = b1).
      {
        apply Nat.le_antisymm.
        - apply Nat.le_trans with (m := b2 + l2).
          apply Heqv2. apply H.
        - apply Heqv1.
      }
      exfalso.
      apply HNOTBEG. left. assumption.
  }
Qed.

Lemma inrange2_forallb:
  forall i r1 r2
         (HIN:List.forallb (in_range i) (r1::r2::nil) = true),
    in_range i r1 = true /\ in_range i r2 = true.
Proof.
  intros.
  simpl in HIN.
  rewrite andb_true_r in HIN.
  rewrite andb_true_iff in HIN.
  assumption.
Qed.


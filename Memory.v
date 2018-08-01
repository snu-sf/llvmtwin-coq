Require Import Common.
Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import PeanoNat.
Require Import Omega.
Require Import sflib.
Require Import Sorting.Permutation.

Module Ir.

(* Pointer value is 16 bits.
   The reason why it is not set as 32 or 64 is that sometimes
   it makes simpl and some tactics (almost) stop :( *)
Parameter PTRSZ : nat.
Axiom PTRSZ_def: PTRSZ = 16.

(* The size of memory. *)
Definition MEMSZ := Nat.shiftl 1 PTRSZ.
(* # of twin blocks. *)
Definition TWINCNT := 3.
(* A maximum value of alignment that will guarantee
   success of machine-level memory access in this target.
   A pointer returned by malloc() will have this alignment. *)
Definition SYSALIGN := 4.

Definition blockid := nat.
Definition callid := nat.
Definition time := nat.

Inductive ptrval :=
(*
-- Log(l, o) where 0 <= o < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
*)
| plog: blockid -> nat -> ptrval
(*
- Phy(o, I, cid) where 0 <= o, i(¡ô I) < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
*)
| pphy: nat -> list nat -> option callid -> ptrval.


(* NULL pointer. *)
Definition NULL := pphy 0 nil None.


Lemma MEMSZ_pos:
  0 < Ir.MEMSZ.
Proof.
  unfold Ir.MEMSZ.
  destruct (0 =? Nat.shiftl 1 Ir.PTRSZ) eqn:H.
  { rewrite PeanoNat.Nat.eqb_eq in H.
    symmetry in H.
    rewrite Nat.shiftl_eq_0_iff in H. congruence. }
  { rewrite PeanoNat.Nat.eqb_neq in H. omega. }
Qed.

Lemma MEMSZ_nonzero:
Ir.MEMSZ <> 0.
Proof.
  unfold Ir.MEMSZ.
  rewrite Ir.PTRSZ_def.
  intros HH. simpl in HH.
  repeat (rewrite Nat.double_twice in HH).
  omega.
Qed.



(* Are two pointers equivalent? *)
Definition ptr_eqb (p1 p2:ptrval): bool :=
  match (p1, p2) with
  | (plog bid1 ofs1, plog bid2 ofs2) =>
    Nat.eqb bid1 bid2 && Nat.eqb ofs1 ofs2
  | (pphy ofs1 I1 cid1, pphy ofs2 I2 cid2) =>
    Nat.eqb ofs1 ofs2 &&
    @list_inclb nat Nat.eq_dec I1 I2 &&
    @list_inclb nat Nat.eq_dec I2 I1 &&
    match (cid1, cid2) with
    | (Some c1, Some c2) => Nat.eqb c1 c2
    | (None, None) => true
    | (_, _) => false
    end
  | (_, _) => false
  end.

Lemma ptr_eqb_refl:
  forall (p:ptrval), ptr_eqb p p = true.
Proof.
  intros.
  destruct p; unfold ptr_eqb.
  - repeat (rewrite Nat.eqb_refl). reflexivity.
  - rewrite Nat.eqb_refl.
    rewrite list_inclb_refl.
    destruct o. rewrite Nat.eqb_refl. reflexivity. reflexivity.
Qed.


(* block types.
   stack: a block in stack
   heap: a block in heap
   global: a global variable
   function: a function variable *)
Inductive blockty :=
| stack | heap | global | function.


Module Bit.

(* Definition of a bit. *)
Inductive t :=
| bint: bool -> t
(* (p, i). Note that 0 <= i < PTRSZ is kept as invariant. *)
| baddr: ptrval -> nat -> t
| bpoison: t.

Definition zero := bint false.
Definition one := bint true.
Definition null (i:nat) := baddr NULL i.


Definition bools_to_bit (bs:list bool): list t :=
  List.map (fun b => bint b) bs.

Fixpoint erase_lzerobits (bits:list t): list t :=
  match bits with
  | nil => nil
  | (bint h)::t =>
    match h with | false => erase_lzerobits t | true => bits
    end
  | x => x
  end.

Definition erase_hzerobits (bits:list t): list t :=
  List.rev (erase_lzerobits (List.rev bits)).

Definition add_lzerobits (bits:list t) (n:nat): list t :=
  List.repeat (bint false) n ++ bits.

Definition add_hzerobits (bits:list t) (n:nat): list t :=
  bits ++ List.repeat (bint false) n.

(**************************************************
             Number <-> bits (list bool)
 *************************************************)

Fixpoint pos_to_bits (n:positive): list t :=
  match n with
  | xH => (bint true)::nil
  | xI n' => (bint true)::(pos_to_bits n')
  | xO n' => (bint false)::(pos_to_bits n')
  end.
Definition N_to_bits (n:N): list t :=
  match n with
  | N0 => nil
  | Npos p => pos_to_bits p
  end.

Eval compute in N_to_bits 0%N. (* nil *)
Eval compute in N_to_bits 10%N. (* [f,t,f,t] *)

Fixpoint _bits_to_pos (bits:list t): positive :=
  match bits with
  | nil => xH
  | (bint true)::nil => xH
  | (bint h)::t => (if h then xI else xO) (_bits_to_pos t)
  | _ => xH
  end.
Definition bits_to_pos (bits:list t): positive :=
  _bits_to_pos (erase_hzerobits bits).

Definition bits_to_N (bits:list t): N :=
  match bits with
  | nil => N0
  | _ => Npos (bits_to_pos bits)
  end.

Definition nonzero (b:t): bool :=
  match b with
  | bint false => false
  | _ => true
  end.


Eval compute in bits_to_N nil. (* 0 *)
Eval compute in bits_to_N (bint true::bint false::bint true::nil). (* 5 *)
Eval compute in erase_lzerobits (bint false::bint false::bint true::nil).
Eval compute in erase_hzerobits (bint false::bint false::bint true::bint false::nil).
Eval compute in add_lzerobits (bint true::bint false::bint true::nil) 2.
Eval compute in add_hzerobits (bint true::bint false::bint true::nil) 2.

(**********************************************
            Lemmas about bit.
 **********************************************)

Lemma erase_lzerobits_app:
  forall (l1 l2:list t)
         (HNOTIN:List.existsb nonzero l1 = true),
    erase_lzerobits (l1 ++ l2) = (erase_lzerobits l1) ++ l2.
Proof.
  intros.
  induction l1.
  - simpl in HNOTIN. inversion HNOTIN.
  - simpl in HNOTIN.
    simpl.
    destruct a.
    + destruct b. simpl. reflexivity.
      simpl in HNOTIN.
      apply IHl1 in HNOTIN.
      assumption.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma pos_to_bits_nonzero:
  forall (p:positive), List.existsb nonzero (pos_to_bits p) = true.
Proof.
  intros.
  induction p.
  - unfold pos_to_bits.
    simpl. reflexivity.
  - unfold pos_to_bits. simpl. fold pos_to_bits. assumption.
  - simpl. reflexivity.
Qed.

Lemma erase_hzerobits_pos_to_bits:
  forall (p:positive), erase_hzerobits (pos_to_bits p) = pos_to_bits p.
Proof.
  intros.
  induction p.
  - unfold erase_hzerobits.
    unfold pos_to_bits.
    simpl.
    rewrite erase_lzerobits_app.
    + rewrite rev_app_distr.
      simpl. fold pos_to_bits.
      unfold erase_hzerobits in IHp.
      rewrite IHp. reflexivity.
    + fold pos_to_bits. rewrite existsb_rev.
      apply pos_to_bits_nonzero.
  - unfold erase_hzerobits.
    simpl.
    rewrite erase_lzerobits_app.
    + rewrite rev_app_distr.
      simpl. unfold erase_hzerobits in IHp. rewrite IHp. reflexivity.
    + rewrite existsb_rev. apply pos_to_bits_nonzero.
  - reflexivity.
Qed.

Lemma pos_to_bits_nonnil:
  forall (p:positive), ~ (pos_to_bits p = nil).
Proof.
  intros.
  destruct p; intros H; inversion H.
Qed.

Lemma pos_bits_pos:
  forall (p:positive), bits_to_pos (pos_to_bits p) = p.
Proof.
  intros.
  unfold bits_to_pos.
  rewrite erase_hzerobits_pos_to_bits.
  induction p.
  - remember (pos_to_bits p) as bs.
    destruct bs. exfalso. eapply pos_to_bits_nonnil. rewrite <- Heqbs. reflexivity.
    simpl.
    rewrite <- Heqbs.
    simpl in *.
    destruct t0.
    + destruct b. rewrite IHp. reflexivity.
      rewrite IHp. reflexivity.
    + rewrite <- IHp. reflexivity.
    + rewrite <- IHp. reflexivity.
  - simpl.
    rewrite IHp. reflexivity.
  - reflexivity.
Qed.

Lemma N_bits_N:
  forall (n:N), bits_to_N (N_to_bits n) = n.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - unfold bits_to_N.
    unfold N_to_bits.
    rewrite pos_bits_pos.
    assert (~ pos_to_bits p = nil).
    { apply pos_to_bits_nonnil. }
    destruct (pos_to_bits p).
    { exfalso. apply H. reflexivity. }
    { reflexivity. }
Qed.

End Bit.


Module Byte.

(* Definition of a byte. *)
Structure t := mk
 {b0:Bit.t;
  b1:Bit.t;
  b2:Bit.t;
  b3:Bit.t;
  b4:Bit.t;
  b5:Bit.t;
  b6:Bit.t;
  b7:Bit.t}.

Definition zero := mk Bit.zero Bit.zero Bit.zero Bit.zero
                      Bit.zero Bit.zero Bit.zero Bit.zero.
Definition one  := mk Bit.one Bit.zero Bit.zero Bit.zero
                      Bit.zero Bit.zero Bit.zero Bit.zero.
Definition mone := mk Bit.one Bit.one Bit.one Bit.one
                      Bit.one Bit.one Bit.one Bit.one.
Definition imax := mk Bit.zero Bit.one Bit.one Bit.one
                      Bit.one Bit.one Bit.one Bit.one.
Definition imin := mk Bit.one Bit.zero Bit.zero Bit.zero
                      Bit.zero Bit.zero Bit.zero Bit.zero.

Definition null i := mk (Bit.null (8*i))   (Bit.null (8*i+1)) (Bit.null (8*i+2))
                        (Bit.null (8*i+3)) (Bit.null (8*i+4)) (Bit.null (8*i+5))
                        (Bit.null (8*i+6)) (Bit.null (8*i+7)).

Definition poison := mk Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison
                        Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison.

Fixpoint from_bits (bs:list Bit.t): list t :=
  match bs with
  | nil => nil
  | b1::nil =>
    (mk b1 Bit.bpoison Bit.bpoison Bit.bpoison
        Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison)::nil
  | b1::b2::nil =>
    (mk b1 b2 Bit.bpoison Bit.bpoison
        Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison)::nil
  | b1::b2::b3::nil =>
    (mk b1 b2 b3 Bit.bpoison
        Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison)::nil
  | b1::b2::b3::b4::nil =>
    (mk b1 b2 b3 b4
        Bit.bpoison Bit.bpoison Bit.bpoison Bit.bpoison)::nil
  | b1::b2::b3::b4::b5::nil =>
    (mk b1 b2 b3 b4
        b5 Bit.bpoison Bit.bpoison Bit.bpoison)::nil
  | b1::b2::b3::b4::b5::b6::nil =>
    (mk b1 b2 b3 b4
        b5 b6 Bit.bpoison Bit.bpoison)::nil
  | b1::b2::b3::b4::b5::b6::b7::nil =>
    (mk b1 b2 b3 b4
        b5 b6 b7 Bit.bpoison)::nil
  | b1::b2::b3::b4::b5::b6::b7::b8::t =>
    (mk b1 b2 b3 b4
        b5 b6 b7 b8)::from_bits t
  end.

Definition to_bits (bs:list t): list Bit.t :=
  List.concat (List.map (fun b =>
        b.(b0)::b.(b1)::b.(b2)::b.(b3)::b.(b4)::b.(b5)::b.(b6)::b.(b7)::nil)
        bs).

(* Check whether bs have all integer bits.
   If it have, return the integer. *)
Definition getint (bs: list Byte.t) (bitsz:nat): option N :=
  let bits := List.firstn bitsz (to_bits bs) in
  if (List.forallb (fun b => match b with | Bit.bint _ => true | _ => false end)
                   bits) then
    Some (Bit.bits_to_N bits)
  else None.

Definition ofint (i:N) (bitsz:nat): list Byte.t :=
  let bits := Bit.N_to_bits i in
  from_bits (Bit.add_hzerobits bits (bitsz - List.length bits)).


Eval compute in getint (zero::zero::nil) 2.
Eval compute in getint (one::zero::nil) 2.
Eval compute in ofint (10%N) 9.

(* Check whether b has 8 pointer bits (p, i), (p, i + 1, ..)
   If it has, this returns (p, i). *)
Definition getpbits (b: Byte.t): option (ptrval * nat) :=
  match (b.(b0), b.(b1), b.(b2), b.(b3), b.(b4), b.(b5), b.(b6), b.(b7)) with
  | (Bit.baddr p0 n0, Bit.baddr p1 n1,
     Bit.baddr p2 n2, Bit.baddr p3 n3,
     Bit.baddr p4 n4, Bit.baddr p5 n5,
     Bit.baddr p6 n6, Bit.baddr p7 n7) =>
    if (Nat.eqb n1 (1 + n0)) && (Nat.eqb n2 (2 + n0)) && (Nat.eqb n3 (3 + n0)) &&
       (Nat.eqb n4 (4 + n0)) && (Nat.eqb n5 (5 + n0)) && (Nat.eqb n6 (6 + n0)) &&
       (Nat.eqb n7 (7 + n0)) &&
       ptr_eqb p0 p1 && ptr_eqb p0 p2 && ptr_eqb p0 p3 && ptr_eqb p0 p4 &&
       ptr_eqb p0 p5 && ptr_eqb p0 p6 && ptr_eqb p0 p7 then
      Some (p0, n0)
    else None
  | (_, _, _, _, _, _, _, _) => None
  end.

(* Check whether bs have all pointer bits.
   If it have, return the integer. *)
Definition getptr (bs:list Byte.t): option ptrval :=
  if Nat.eqb (8 * List.length bs) PTRSZ then
    (* Should be the size of pointer *)
    match bs with
    | nil => None (* This wouldn't happen. *)
    | hd::tl =>   (* hd is the first byte of the pointer value. *)
      let hdp := getpbits hd in
      match (hdp) with
      | Some (p0, 0) => (* lowest byte has the lowest portion of pointer p0. *)
        let tl' := List.map getpbits tl in
        (* Is i'th byte a byte of (p0, i)? *)
        let alleq := List.fold_left
                 (fun i pb =>
                    match i, pb with
                    | _, None => None
                    | None, _ => None
                    | Some i, Some (p, ofs) =>
                      if ptr_eqb p p0 && Nat.eqb ofs (8 + i) then
                        Some ofs
                      else None
                    end)
                 tl' (Some 0) in
        match alleq with
        | None => None
        | Some _ => Some p0
        end
      | _ => None (* Bits of the first byte isn't the zero-th byte of pointer value *)
      end
    end
  else None.

Definition ofptr (bs:ptrval): list Byte.t
:= from_bits
     (List.map (fun i => Bit.baddr i.(snd) i.(fst))
               (number_list (List.repeat bs PTRSZ))).

Eval compute in getpbits (null 0).
Eval compute in getpbits (null 1).
Eval compute in getptr ((null 0)::nil). (* None *)
Eval compute in getptr ((null 0)::(null 1)::nil). (* Some (pphy (0, nil, None)). *)
Eval compute in getptr ((null 0)::(null 1)::(null 2)::nil). (* None *)

(********************************************
         Lemmas about bits & bytes.
 ********************************************)

Lemma from_bits_nonnil:
  forall b bs,
    nil <> from_bits (b::bs).
Proof.
  intros.
  destruct bs as [| b1 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b2 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b3 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b4 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b5 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b6 bs].
  { intros H. simpl in H. inversion H. }
  destruct bs as [| b7 bs].
  { intros H. simpl in H. inversion H. }
  intros H. simpl in H. inversion H.
Qed.

Lemma from_bits_inv:
  forall bytes l1 l2 a
         (HLEN:List.length l1 = 8)
         (H:a :: bytes = from_bits (l1 ++ l2)),
  bytes = from_bits l2.
Proof.
  intros.
  destruct l1 as [| h0 l1]. inversion HLEN.
  destruct l1 as [| h1 l1]. inversion HLEN.
  destruct l1 as [| h2 l1]. inversion HLEN.
  destruct l1 as [| h3 l1]. inversion HLEN.
  destruct l1 as [| h4 l1]. inversion HLEN.
  destruct l1 as [| h5 l1]. inversion HLEN.
  destruct l1 as [| h6 l1]. inversion HLEN.
  destruct l1 as [| h7 l1]. inversion HLEN.
  destruct l1 as [| h8 l1].
  simpl.
  simpl in H. inversion H. reflexivity.
  simpl in HLEN. omega.
Qed.

Lemma from_bits_to_bits:
  forall (ls:list Bit.t),
    to_bits (from_bits ls) =
    ls ++ List.repeat (Bit.bpoison)
       (Nat.modulo ((8 - Nat.modulo (List.length ls) 8)) 8).
Proof.
  intros.
  assert (HB:=list_segmentize8_r ls).
  remember (from_bits ls) as bytes.
  generalize dependent ls.
  induction bytes.
  - intros.
    destruct ls.
    + simpl. reflexivity.
    + simpl in Heqbytes.
      destruct ls as [ | h1 ls].
      inversion Heqbytes.
      destruct ls as [ | h2 ls].
      inversion Heqbytes.
      destruct ls as [ | h3 ls].
      inversion Heqbytes.
      destruct ls as [ | h4 ls].
      inversion Heqbytes.
      destruct ls as [ | h5 ls].
      inversion Heqbytes.
      destruct ls as [ | h6 ls].
      inversion Heqbytes.
      destruct ls as [ | h7 ls].
      inversion Heqbytes.
      inversion Heqbytes.
  - intros.
    assert (to_bits (a::bytes) = (to_bits (a::nil)) ++ to_bits bytes).
    { unfold to_bits.
      simpl. reflexivity. }
    rewrite H. clear H.
    (* ls is a list of bit. *)
    destruct HB as [ls1 [ls2 [HB1 [HB2 HB3]]]].
    (* ls = ls1 ++ ls2.
       |ls2| < 8 *)
    assert (ls1 = nil \/
            (exists ls1' ls1'', List.length ls1' = 8 /\ ls1 = ls1' ++ ls1'')).
    { remember (List.length ls1) as n1.
      assert (HN1 := Nat.eq_dec n1 0).
      destruct HN1.
      - left. rewrite Heqn1 in e.
        rewrite length_zero_iff_nil in e. congruence. 
      - assert (HSP:=list_split8_l ls1 n1 Heqn1 HB2).
        destruct HSP as [ls1h [ls1t [HSP1 [HSP2 HSP3]]]].
        assumption.
        right.
        exists ls1h.
        exists ls1t.
        split. assumption. assumption.
    }
    (* ls = ls1 ++ ls2
       ls --from_bits--> a::bytes
       |ls2| < 8 *)
    destruct H as [H | H].
    + rewrite H in HB1.
      (* ls1 = nil
         bytes = nil *)
      simpl in HB1.
      rewrite HB1 in *.
      clear HB1.
      destruct ls2 as [| h20 ls2].
      { simpl in Heqbytes. inversion Heqbytes. }
      destruct ls2 as [| h21 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h22 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h23 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h24 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h25 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h26 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      destruct ls2 as [| h27 ls2].
      { simpl in Heqbytes.
        inversion Heqbytes.
        rewrite H2 in *. clear H2.
        reflexivity. }
      simpl in HB3.
      omega.
    + destruct H as [ls1head [ls1tail H]].
      destruct H as [H1 H2].
      rewrite H2 in HB1.
      rewrite HB1.
      rewrite HB1 in Heqbytes.
      (* l ++ m ++ n = (l ++ m) ++ n *)
      rewrite <- app_assoc with (l := ls1head) (m := ls1tail)
         (n := ls2).
      rewrite <- app_assoc with (l := ls1head) (m := ls1tail ++ ls2).
      replace (length (ls1head ++ ls1tail ++ ls2) mod 8) with
              (length (ls1tail ++ ls2) mod 8).
      rewrite <- IHbytes with (ls := ls1tail++ls2).
      destruct ls1head as [| h0 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h1 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h2 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h3 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h4 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h5 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h6 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h7 ls1head].
      { simpl in H1. inversion H1. }
      destruct ls1head as [| h8 ls1head].
      { simpl in Heqbytes.
        inversion Heqbytes.
        simpl. reflexivity. }
      { simpl in H1. inversion H1. }
      exists ls1tail. exists ls2.
      split. reflexivity.
      split. rewrite H2 in HB2.
      rewrite app_length in HB2.
      rewrite H1 in HB2.
      rewrite <- Nat.add_mod_idemp_l in HB2.
      simpl in HB2.
      simpl. assumption.
      omega.
      assumption.
      eapply from_bits_inv.
      eassumption. rewrite <- app_assoc in Heqbytes. eassumption.
      rewrite app_length with (l := ls1head).
      rewrite H1.
      rewrite <- Nat.add_mod_idemp_l.
      simpl. reflexivity.
      omega.
Qed.

Lemma N_to_bits_notbaddr:
  forall n b
         (HIN:List.In b (Ir.Bit.N_to_bits n)),
    forall p ofs, b <> Ir.Bit.baddr p ofs.
Proof.
  intros n b HIN.
  generalize dependent b.
  induction n.
  { intros. simpl in HIN. inv HIN. }
  { intros.
    simpl in HIN.
    generalize dependent b.
    induction p.
    { simpl. intros. destruct HIN. rewrite <- H. ss.
      apply IHp in H. ss. }
    { simpl. intros. destruct HIN. rewrite <- H. ss.
      apply IHp in H. ss. }
    { simpl. intros. inv HIN. ss. inv H. }
  }
Qed.

Lemma add_hzerobits_notbaddr:
  forall bits n
         (HFORALL:List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs) bits),
    List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs)
                (Ir.Bit.add_hzerobits bits n).
Proof.
  intros.
  unfold Ir.Bit.add_hzerobits.
  apply Forall_app2. ss.
  apply Forall_repeat. ss.
Qed.

Lemma from_bits_notbaddr:
  forall bits
         (HFORALL:List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs) bits),
    List.Forall (fun b =>
                   forall p ofs, b.(Ir.Byte.b0) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b1) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b2) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b3) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b4) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b5) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b6) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b7) <> Ir.Bit.baddr p ofs) (Ir.Byte.from_bits bits).
Proof.
  intros.
  remember (Ir.Byte.from_bits bits) as byt.
  generalize dependent bits.
  induction byt.
  { simpl. intros. constructor. }
  { intros.
    destruct bits. simpl in Heqbyt.  inv Heqbyt.
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7 . inv H8.
      repeat (split; try congruence).
      constructor. }
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7 . inv H8. inv H9.
      repeat (split; try congruence).
    remember (t0::t1::t2::t3::t4::t5::t6::t7::nil) as l.
    assert (t0::t1::t2::t3::t4::t5::t6::t7::bits = l ++ bits).
    { rewrite Heql. reflexivity. }
    rewrite H in *.
    apply Forall_app in HFORALL. inv HFORALL.
    exploit IHbyt. eassumption. ss. eauto.
    }
  }
Qed.

End Byte.



Module MemBlock.

(* Block := (t, r, n, a, c, P)
   Note that |P| == twin# is kept as invariant. *)
Structure t := mk
  {
    bt: blockty; r:time * option time;
    n: nat; a: nat; c:list (Byte.t);
    P: list nat
  }.

(* Returns (start_ofs, size)s that include all twin blocks. *)
Definition P_ranges (mb:t):list (nat * nat) :=
  List.map (fun ofs => (ofs, mb.(n))) mb.(P).

(* Returns integer address of the block. *)
Definition addr (mb:t): nat :=
  List.hd 0 mb.(P).

(* Returns (start_ofs, size) of the using one. *)
Definition P0_range (mb:t): nat * nat :=
  (addr mb, mb.(n)).


(* Well-formendess of a memory block. *)
Structure wf (mb:t) := mkWf
  {
    (* wf_tcond: Wellformedness of lifetime of a block. *)
    wf_tcond: forall t (FREED:mb.(r).(snd) = Some t), mb.(r).(fst) < t;
    (* wf_clen: length of bytes is equivalent to n. *)
    wf_clen: List.length mb.(c) = mb.(n);
    (* wf_poslen: There's no zero-size block in the memory.
       In this formalization, malloc(0) returns NULL, so this invariant
       holds. *)
    wf_poslen: no_empty_range (P_ranges mb) = true;
    (* wf_align: alignment criteria *)
    wf_align: forall p (HAS:List.In p mb.(P)), Nat.modulo p mb.(a) = 0;
    (* wf_mem: Note that this is "<", not "<=", because p + n wouldn't
       be representable in 2^32 bits *)
    wf_inmem: forall p (HAS:List.In p mb.(P)), p + mb.(n) < MEMSZ;
    (* wf_notnull: block starting offset cannot be 0
       (because this formalization assumes that address space is always 0) *)
    wf_notnull: forall p (HAS:List.In p mb.(P)), ~ (p = 0);
    (* all twin blocks are disjoint *)
    wf_disj: disjoint_ranges (P_ranges mb) = true;
    (* has correct number of twin blocks. *)
    wf_twin: List.length mb.(P) = TWINCNT
  }.

(* is block t alive? *)
Definition alive (mb:t): bool :=
  match mb.(r).(snd) with
  | None => true | Some _ => false
  end.

(* Is block t alive before time the_time? *)
Definition alive_before (the_time:nat) (mb:t): bool :=
  Nat.ltb mb.(r).(fst) the_time.

Definition lifetime_to_range (cur_time:nat) (mb:t): nat * nat :=
  (mb.(r).(fst),
   match mb.(r).(snd) with
   | None => cur_time | Some r => r
   end - mb.(r).(fst)).

(* 0 <= ofs <= block size of mb? *)
Definition inbounds (ofs:nat) (mb:t): bool :=
  Nat.leb ofs mb.(n).

(* start_ofs <= ofs <= start_ofs + block size of mb? *)
Definition inbounds_abs (ofs':nat) (mb:t): bool :=
  in_range ofs' (P0_range mb).

(* Get bytes in (offset, offset +len) *)
Definition bytes (mb:t) (ofs len:nat): list (Byte.t) :=
  List.firstn len (List.skipn ofs mb.(c)).

(* Update bytes. *)
Definition set_bytes (mb:t) (ofs:nat) (bytes:list (Byte.t)): t :=
  mk mb.(bt) mb.(r) mb.(n) mb.(a)
     (List.firstn ofs (mb.(c)) ++ bytes ++
      List.skipn (ofs + List.length bytes) mb.(c))
     mb.(P).

(* Set the end of lifetime if it was alive. *)
Definition set_lifetime_end (mb:t) (newt:time): option t :=
  if alive mb then
    Some (mk mb.(bt) (mb.(r).(fst), Some newt)
               mb.(n) mb.(a) mb.(c) mb.(P))
  else None.

(**********************************************
      Lemmas&Theorems about MemBlock.
 **********************************************)

Lemma P_P0_range_lsubseq:
  forall mb (HWF:wf mb),
    lsubseq (P_ranges mb) ((P0_range mb)::nil).
Proof.
  intros.
  unfold P_ranges.
  unfold P0_range.
  destruct (MemBlock.P mb) as [| P0 Pt] eqn:HP1.
  { (* cannot be nil. *)
    assert (List.length (MemBlock.P mb) = 0).
    { rewrite HP1. reflexivity. }
    rewrite (MemBlock.wf_twin) in H. inversion H. assumption.
  }
  unfold addr.
  rewrite HP1. simpl.
  constructor.
  constructor.
Qed.

Lemma inbounds_inbounds_abs:
  forall (mb:t) ofs ofs_abs
         (HABS: ofs_abs = ofs + addr mb),
    inbounds ofs mb = inbounds_abs ofs_abs mb.
Proof.
  intros.
  unfold inbounds.
  unfold inbounds_abs.
  rewrite HABS.
  unfold Common.in_range.
  unfold Ir.MemBlock.P0_range.
  remember (Ir.MemBlock.addr mb) as addr.
  remember (Ir.MemBlock.n mb) as n.
  simpl.
  assert (PeanoNat.Nat.leb addr (ofs + addr) = true).
  {
    rewrite PeanoNat.Nat.leb_le.
    apply Plus.le_plus_r.
  }
  rewrite H.
  simpl.
  rewrite PeanoNat.Nat.add_comm with (n := ofs) (m := addr).
  remember (PeanoNat.Nat.leb (addr + ofs) (addr + n)) as flag.
  symmetry in Heqflag.
  destruct flag.
  - rewrite PeanoNat.Nat.leb_le in Heqflag.
    apply Plus.plus_le_reg_l in Heqflag.
    rewrite PeanoNat.Nat.leb_le.
    assumption.
  - rewrite PeanoNat.Nat.leb_nle in Heqflag.
    rewrite PeanoNat.Nat.leb_nle.
    intros H'.
    apply Heqflag.
    apply Plus.plus_le_compat_l.
    assumption.
Qed.

Lemma inbounds_mod:
  forall mb (HWF:Ir.MemBlock.wf mb) ofs
         (HINB:Ir.MemBlock.inbounds ofs mb = true),
    (Ir.MemBlock.addr mb + ofs) mod Ir.MEMSZ = Ir.MemBlock.addr mb + ofs.
Proof.
  intros.
  rewrite Nat.mod_small. reflexivity.
  inv HWF.
  unfold Ir.MemBlock.inbounds in HINB.
  rewrite PeanoNat.Nat.leb_le in HINB.
  eapply Nat.le_lt_trans with (m := Ir.MemBlock.addr mb +Ir.MemBlock.n mb).
  omega.
  apply wf_inmem0.
  unfold Ir.MemBlock.addr.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin0. inv wf_twin0.
  simpl. 
  left. reflexivity.
Qed.

(* Thanks to twin blocks, size of a block cannot equal to or be larger than a half of
   memory size. *)
Lemma blocksz_lt:
  forall mb (HWF:Ir.MemBlock.wf mb),
    ~ (Ir.MemBlock.n mb >= Nat.shiftl 1 (Ir.PTRSZ - 1)).
Proof.
  intros.
  intros H.
  inv HWF.
  unfold Ir.MemBlock.P_ranges in wf_disj0.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin0. inv wf_twin0.
  destruct l. simpl in wf_twin0. inv wf_twin0.
  simpl in wf_disj0.
  rewrite andb_true_iff in wf_disj0.
  rewrite andb_true_iff in wf_disj0.
  rewrite andb_true_iff in wf_disj0.
  destruct wf_disj0.
  destruct H0. clear H1. clear H2.
  unfold disjoint_range in H0.
  rewrite orb_true_iff in H0.
  rewrite PeanoNat.Nat.leb_le in H0.
  rewrite PeanoNat.Nat.leb_le in H0.
  assert (Ir.MEMSZ = (Nat.shiftl 1 (Ir.PTRSZ - 1)) +
                     (Nat.shiftl 1 (Ir.PTRSZ - 1))).
  { unfold MEMSZ. rewrite Ir.PTRSZ_def. reflexivity. }
  destruct H0.
  { exploit wf_inmem0.
    simpl. right. left. reflexivity.
    intros HH.
    omega.
  }
  { exploit wf_inmem0.
    simpl. left. reflexivity.
    intros HH. omega.
  }
Qed.  
  
Lemma inbounds_abs_lt_MEMSZ:
  forall mb i
         (HWF:Ir.MemBlock.wf mb)
         (HINB:Ir.MemBlock.inbounds_abs i mb = true),
    i < Ir.MEMSZ.
Proof.
  intros.
  unfold Ir.MemBlock.inbounds_abs in HINB.
  unfold in_range in HINB.
  rewrite andb_true_iff in HINB.
  destruct HINB.
  rewrite PeanoNat.Nat.leb_le in H0.
  unfold Ir.MemBlock.P0_range in *.
  simpl in *.
  destruct HWF.
  eapply le_lt_trans.
  eassumption.
  apply wf_inmem0.
  unfold Ir.MemBlock.addr.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin0. unfold Ir.TWINCNT in wf_twin0. congruence.
  simpl. left. reflexivity.
Qed.

Lemma bytes_In_c:
  forall mb ofs len byt b
         (HBYTES:Ir.MemBlock.bytes mb ofs len = byt)
         (HIN:List.In b byt),
    List.In b (Ir.MemBlock.c mb).
Proof.
  intros.
  unfold Ir.MemBlock.bytes in HBYTES.
  rewrite <- HBYTES in HIN.
  eapply firstn_In in HIN; try ss.
  eapply skipn_In in HIN; try ss.
  ss.
Qed.

Lemma n_pos:
  forall mb (HWF:Ir.MemBlock.wf mb),
    Ir.MemBlock.n mb > 0.
Proof.
  intros.
  inv HWF.
  unfold Ir.MemBlock.P_ranges in wf_poslen0.
  unfold no_empty_range in wf_poslen0.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin0. inv wf_twin0.
  simpl in wf_poslen0.
  rewrite andb_true_iff in wf_poslen0.
  destruct wf_poslen0. rewrite PeanoNat.Nat.ltb_lt in H.
  omega.
Qed.

Lemma bytes_length:
  forall mb ofs sz
    (HOFS:ofs + sz <= List.length (Ir.MemBlock.c mb)),
    length (Ir.MemBlock.bytes mb ofs sz) = sz.
Proof.
  intros.
  unfold Ir.MemBlock.bytes.
  remember (Ir.MemBlock.c mb) as c.
  assert (length (firstn sz (skipn ofs c)) = sz).
  {
    assert (exists l1 l2, (c = l1 ++ l2 /\ List.length l1 = ofs)).
    {
      apply app_decompose.
      omega.
    }
    destruct H as [l1 [l2 [H1 H2]]].
    rewrite skipn_app_decompose with (l3 := l1) (l4 := l2).
    assert (exists l2' l3, (l2 = l2' ++ l3 /\ List.length l2' = sz)).
    { apply app_decompose.
      assert (List.length c = List.length l1 + List.length l2).
      { rewrite <- app_length. rewrite H1. reflexivity. }
      rewrite H2 in H. rewrite H in HOFS.
      omega.
    }
    destruct H as [l2' [l3 [H3 H4]]].
    erewrite firstn_app_decompose.
    - eapply H4.
    - eapply H3.
    - assumption.
    - assumption.
    - assumption.
  }
  assumption.
Qed.

Lemma set_bytes_self:
  forall mb ofs sz
    (HOFS:ofs + sz <= List.length (Ir.MemBlock.c mb)),
    Ir.MemBlock.set_bytes mb ofs (Ir.MemBlock.bytes mb ofs sz) = mb.
Proof.
  intros.
  unfold Ir.MemBlock.set_bytes.
  rewrite bytes_length.
  unfold Ir.MemBlock.bytes.
  remember (Ir.MemBlock.c mb) as c.
  assert (firstn ofs c ++ firstn sz (skipn ofs c) ++ skipn (ofs + sz) c
                 = c).
  {
    rewrite app_assoc.
    rewrite firstn_firstn_skipn.
    rewrite firstn_skipn. reflexivity.
  }
  rewrite H.
  rewrite Heqc.
  destruct mb. simpl. reflexivity.
  assumption.
Qed.

Lemma inbounds_abs_addr:
  forall (blk:Ir.MemBlock.t) o ofs
         (HABS:Ir.MemBlock.inbounds_abs o blk = true)
         (HO:o - Ir.MemBlock.addr blk = ofs),
    o = Ir.MemBlock.addr blk + ofs.
Proof.
  intros.
  rewrite <- HO.
  unfold Ir.MemBlock.inbounds_abs in HABS.
  unfold Ir.MemBlock.P0_range in HABS.
  unfold in_range in HABS.
  simpl in HABS.
  rewrite andb_true_iff in HABS.
  destruct HABS.
  rewrite le_plus_minus_r.
  reflexivity.
  apply leb_complete in H.
  assumption.
Qed.

Lemma no_empty_range_P_ranges:
  forall (mb:t) (HSZ:0 < mb.(n)),
    no_empty_range (P_ranges mb) = true.
Proof.
  intros.
  unfold P_ranges.
  induction (P mb).
  - reflexivity.
  - simpl. rewrite <- Nat.ltb_lt in HSZ.
    rewrite HSZ. rewrite IHl. reflexivity.
Qed.

Lemma P_ranges_nonnil:
  forall mb (HWF:wf mb),
    P_ranges mb <> [].
Proof.
  intros.
  inv HWF.
  unfold P_ranges.
  intros HH.
  rewrite <- List.length_zero_iff_nil in HH.
  rewrite List.map_length in HH.
  unfold Ir.TWINCNT in wf_twin0.
  congruence.
Qed.

Lemma P_ranges_no_empty_range:
  forall mb (HWF:wf mb),
    no_empty_range (P_ranges mb) = true.
Proof.
  intros.
  inv HWF.
  assumption.
Qed.

Lemma P0_range_no_empty_range:
  forall mb (HWF:wf mb),
    no_empty_range [P0_range mb] = true.
Proof.
  intros.
  eapply no_empty_range_lsubseq with (l1 := P_ranges mb).
  apply P_ranges_no_empty_range.
  assumption.
  apply P_P0_range_lsubseq.
  assumption.
Qed.

Lemma P_ranges_hd_P0_range:
  forall mb
    (HWF:Ir.MemBlock.wf mb),
    List.hd (0, 0) (Ir.MemBlock.P_ranges mb) = Ir.MemBlock.P0_range mb.
Proof.
  intros.
  unfold Ir.MemBlock.P_ranges.
  unfold Ir.MemBlock.P0_range.
  inv HWF.
  unfold Ir.TWINCNT in *.
  unfold Ir.MemBlock.addr.
  destruct (Ir.MemBlock.P mb).
  { inv wf_twin0. }
  { reflexivity. }
Qed.

Lemma addr_P_In:
  forall mb (HWF:Ir.MemBlock.wf mb),
    List.In (Ir.MemBlock.addr mb) (Ir.MemBlock.P mb).
Proof.
  intros.
  inv HWF.
  unfold Ir.MemBlock.addr.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin0. unfold Ir.TWINCNT in wf_twin0. congruence.
  simpl. left. reflexivity.
Qed.

End MemBlock.


(* Memory. *)

Module Memory.

Structure t := mk
  {
    mt:time; blocks:list (blockid * MemBlock.t);
    calltimes: list (callid * option time);
    fresh_bid: blockid
  }.

(* Returns a list of alive blocks in the memory. *)
Definition alive_blocks (m:t): list (blockid * MemBlock.t) :=
  List.filter (fun xb => MemBlock.alive xb.(snd)) m.(blocks).

(* Returns a list of allocated ranges (including twins).
   Each element has a form of (begin-index, length). *)
Definition alive_P_ranges (m:t): list (nat * nat) :=
  List.concat (List.map (fun b => MemBlock.P_ranges b.(snd)) (alive_blocks m)).

Definition alive_P0_ranges (m:t): list (nat * nat) :=
  List.map (fun x => MemBlock.P0_range x.(snd)) (alive_blocks m).

(* Returns true if range r never overlaps with other alive blocks,
   false otherwise. *)
Definition allocatable (m:t) (r:list (nat * nat)):bool :=
  disjoint_ranges (r++(alive_P_ranges m)).

(* Returns blocks which are alive & has abs_ofs as inbounds *)
Definition inbounds_blocks (m:t) (abs_ofs:nat)
: list (blockid * MemBlock.t) :=
  snd (disjoint_include2 (alive_P0_ranges m) (alive_blocks m) abs_ofs).

(* Returns blocks which are alive & has abs_ofss as inbounds. *)
Definition inbounds_blocks2 (m:t) (abs_ofss:list nat)
: list (blockid * MemBlock.t) :=
  snd
    (List.fold_left
       (fun blks_and_ranges abs_ofs =>
          disjoint_include2 blks_and_ranges.(fst) blks_and_ranges.(snd) abs_ofs)
       abs_ofss
       ((alive_P0_ranges m), (alive_blocks m))).

(* Returns an alive block which have beginning address at abs_ofs. *)
Definition zeroofs_block (m:t) (abs_ofs:nat)
: option (blockid * MemBlock.t) :=
  match (inbounds_blocks2 m (abs_ofs::abs_ofs+1::nil)) with
  | nil => None
  | t =>
    match (List.filter (fun mb => Nat.eqb (MemBlock.addr mb.(snd)) abs_ofs) t) with
    | nil => None
    | h::t' => Some h
    end
  end.


(* Add a new memory block. *)
Definition new (m:t) (t:blockty) (n:nat) (a:nat) (c:list Byte.t) (P:list nat)
: Memory.t * blockid :=
  (mk (1 + m.(mt)) (* update time *)
     ((m.(fresh_bid), (MemBlock.mk t (m.(mt), None) n a c P))::m.(blocks)) (* add block *)
     m.(calltimes) (* no update to call times *)
     (1 + m.(fresh_bid)) (* update block id *)
   , m.(fresh_bid)).

(* Get the memory block which has id i. *)
Definition get (m:t) (i:blockid): option MemBlock.t :=
  match (list_find_key m.(blocks) i) with
  | nil => None
  | a::b => Some a.(snd)
  end.

(* Replace the memory block which has id i. *)
Definition set (m:t) (i:blockid) (mb:MemBlock.t): t :=
  mk m.(mt)
     (list_set m.(blocks) i mb)
     m.(calltimes) m.(fresh_bid).

Definition incr_time (m:t): t :=
  mk (1 + m.(mt)) m.(blocks) m.(calltimes) m.(fresh_bid).

(* Free existing block.
   If free fails, returns None *)
Definition free (m:t) (i:blockid): option t :=
  match (get m i) with
  | Some mb =>
    match (MemBlock.bt mb) with
    | heap =>
      if MemBlock.alive mb then
        match (MemBlock.set_lifetime_end mb m.(mt)) with
        | Some mb' => Some (set (incr_time m) i mb')
        | None => None
        end
      else None
    | _ => None
    end
  | None => None
  end.

Definition callbegin (m:t) (cid:callid): t :=
  mk m.(mt) m.(blocks) ((cid, Some m.(mt))::m.(calltimes)) m.(fresh_bid).

Definition callend (m:t) (cid:callid): t :=
  mk m.(mt) m.(blocks) ((cid, None)::m.(calltimes)) m.(fresh_bid).

Definition calltime (m:t) (cid:callid): option time :=
  match (List.filter (fun i2 => Nat.eqb i2.(fst) cid) m.(calltimes)) with
  | nil => None
  | h::t => h.(snd)
  end.



(* Well-formedness of memory. *)
Structure wf (m:t) :=
  {
    (* all blocks in memory are well-formed. *)
    wf_blocks: forall i p (HAS:List.In (i, p) m.(blocks)), MemBlock.wf p;
    (* each block has unique id. *)
    wf_uniqueid: List.NoDup (list_keys m.(blocks));
    (* all existing blocks have id smaller than fresh_bid. *)
    wf_newid: List.forallb (fun bid => Nat.ltb bid m.(fresh_bid))
                           (list_keys m.(blocks)) = true;
    (* all alive blocks have disjoint addresses. *)
    wf_disjoint: disjoint_ranges (alive_P_ranges m) = true;
    (* two blocks which have overlapping life times have
       disjoint addresses. generalizd version of wf_disjoint. *)
    wf_disjoint2:
      forall l1 l2 mb1 mb2
             (HGET1:Some mb1 = get m l1)
             (HGET2:Some mb2 = get m l2)
             (HNEQ:l1 <> l2)
             (HOVERLAP:disjoint_range
                         (MemBlock.lifetime_to_range m.(mt) mb1)
                         (MemBlock.lifetime_to_range m.(mt) mb2)
                         = false),
        disjoint_ranges ((MemBlock.P_ranges mb1)++MemBlock.P_ranges mb2) = true;
    (* all blocks are created before memory time. *)
    wf_blocktime_beg: forall i p (HAS:List.In (i, p) m.(blocks)),
        p.(MemBlock.r).(fst) < (mt m);
    (* all blocks' freed time is larger than created time. *)
    wf_blocktime_end:
          forall i p e
                 (HAS:List.In (i, p) m.(blocks))
                 (HEND:Some e = p.(MemBlock.r).(snd)),
            p.(MemBlock.r).(fst) < e /\ e < (mt m)
  }.




(**********************************************
  Lemmas&Theorems about get/set/new/free functions
 **********************************************)      

Lemma get_In:
  forall (m:t) bid blk blks
         (HGET:Some blk = get m bid)
         (HBLK:blks = blocks m),
    List.In (bid, blk) blks.
Proof.
  intros.
  unfold get in HGET.
  rewrite <- HBLK in *.
  remember (list_find_key blks bid) as f.
  destruct f.
  - inversion HGET.
  - inversion HGET.
    assert (p.(fst) = bid).
    { assert (List.forallb (fun i2 => Nat.eqb (fst i2) bid) (p::f) = true).
      rewrite Heqf.
      apply filter_forallb.
      simpl in H.
      rewrite andb_true_iff in H.
      destruct H.
      rewrite Nat.eqb_eq in H.
      assumption.
    }
    rewrite <- H.
    destruct p.
    simpl.
    apply lsubseq_In with (l':=(n,t0)::f).
    simpl. left. reflexivity.
    rewrite Heqf.
    apply lsubseq_filter.
Qed.

Lemma get_not_In:
  forall (m:Ir.Memory.t) bid blk blks
         (HGET:None = Ir.Memory.get m bid)
         (HBLK:blks = Ir.Memory.blocks m),
    ~ List.In (bid, blk) blks.
Proof.
  intros.
  unfold Ir.Memory.get in HGET.
  rewrite <- HBLK in *.
  remember (list_find_key blks bid) as f.
  destruct f.
  - intros HH.
    symmetry in Heqf.
    eapply list_find_key_In_none with (x := (bid, blk)) in Heqf.
    simpl in Heqf. congruence.
    assumption.
  - congruence.
Qed.

Lemma In_get:
  forall m b mb
         (HWF:Ir.Memory.wf m)
         (HIN:List.In (b, mb) (Ir.Memory.blocks m)),
    Some mb = Ir.Memory.get m b.
Proof.
  intros.
  unfold Ir.Memory.get.
  assert (list_find_key (Ir.Memory.blocks m) b = [(b, mb)]).
  { eapply list_find_key_spec.
    assumption.
    inv HWF. assumption. }
  rewrite H. reflexivity.
Qed.

Lemma get_In_key:
  forall (m:t) bid blk blks
         (HGET:Some blk = get m bid)
         (HBLK:blks = blocks m),
    List.In bid (list_keys blks).
Proof.
  intros.
  assert (List.In (bid, blk) blks).
  { eapply get_In; eassumption. }
  eapply list_keys_In. eassumption.
Qed.

Lemma get_incr_time_id:
  forall m bid,
    Ir.Memory.get (Ir.Memory.incr_time m) bid = Ir.Memory.get m bid.
Proof.
  intros.
  unfold Ir.Memory.incr_time.
  unfold Ir.Memory.get.
  reflexivity.
Qed.

Lemma get_set_id:
  forall m bid mb' m' mb
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = Some mb)
         (HSET:m' = Ir.Memory.set m bid mb'),
    Ir.Memory.get m' bid = Some mb'.
Proof.
  intros.
  unfold Ir.Memory.get.
  symmetry in HGET.
  apply Ir.Memory.get_In with (blks := Ir.Memory.blocks m) in HGET.
  apply list_keys_In in HGET.
  assert (List.In (bid, mb') (Ir.Memory.blocks m')).
  { apply list_set_In with (l := Ir.Memory.blocks m).
    assumption.
    unfold Ir.Memory.set in HSET.
    rewrite HSET. reflexivity. }
  remember (list_find_key (Ir.Memory.blocks m') bid) as res.
  assert (List.length res < 2).
  { apply list_find_key_NoDup with (l := Ir.Memory.blocks m') (key := bid).
    destruct m'. inversion HSET. rewrite <- H1.
    destruct HWF. simpl in *.
    assert (NoDup(list_keys blocks0)).
    { rewrite H2. erewrite list_set_keys_eq; try reflexivity. assumption. }
    rewrite H2 in H0. assumption. assumption. }
  assert (List.In (bid, mb') res).
  { rewrite Heqres. eapply list_find_key_In. eassumption. }
  destruct res. inversion H1.
  destruct res.
  simpl in H1. destruct H1 as [H1 | H1]; try inversion H1.
  reflexivity.
  simpl in H0.
  omega.
  reflexivity.
Qed.

Lemma get_set_id_none:
  forall m bid mb' m'
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = None)
         (HSET:m' = Ir.Memory.set m bid mb'),
    Ir.Memory.get m' bid = None.
Proof.
  intros.
  unfold Ir.Memory.get in *.
  unfold Ir.Memory.set in *.
  rewrite HSET. simpl. rewrite list_find_key_set_none. reflexivity.
  des_ifs.
Qed.

Lemma get_set_id_short:
  forall m bid mb' mb0
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = Some mb0),
    Ir.Memory.get (Ir.Memory.set m bid mb') bid = Some mb'.
Proof.
  intros.
  erewrite Ir.Memory.get_set_id with (mb := mb0).
  reflexivity. eapply HWF. assumption. reflexivity.
Qed.

Lemma get_set_exists:
  forall m b bid mb mb'
         (HGET:Some mb = Ir.Memory.get (Ir.Memory.set m b mb') bid),
    exists mb'', Some mb'' = Ir.Memory.get m bid.
Proof.
  intros.
  unfold Ir.Memory.get in *.
  unfold Ir.Memory.set in *.
  simpl in *.
  des_ifs.
  eapply list_find_key_set_none2 with (k' := b) (v := mb') in Heq.
  rewrite Heq in Heq0. ss.
  eexists. ss.
Qed.

Lemma get_set_diff:
  forall m bid mb' m' mb bid'
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = Some mb)
         (HSET:m' = Ir.Memory.set m bid' mb')
         (HDIFF:bid <> bid'),
    Ir.Memory.get m' bid = Some mb.
Proof.
  intros.
  unfold Ir.Memory.get.
  symmetry in HGET.
  rewrite HSET.
  unfold Ir.Memory.set.
  simpl. rewrite list_find_key_set_diffkey.
  unfold Ir.Memory.get in HGET. congruence.
  congruence.
Qed.

Lemma get_set_diff_short:
  forall m bid mb' bid'
         (HWF:Ir.Memory.wf m)
         (HDIFF:bid <> bid'),
    Ir.Memory.get (Ir.Memory.set m bid' mb') bid =
    Ir.Memory.get m bid.
Proof.
  intros.
  unfold Ir.Memory.get.
  unfold Ir.Memory.set.
  simpl. rewrite list_find_key_set_diffkey.
  congruence.
  congruence.
Qed.

Lemma get_set_diff_inv:
  forall m bid mb' mb bid'
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get (Ir.Memory.set m bid' mb') bid = Some mb)
         (HDIFF:bid <> bid'),
    Ir.Memory.get m bid = Some mb.
Proof.
  intros.
  unfold Ir.Memory.get.
  symmetry in HGET.
  unfold Ir.Memory.set in HGET.
  unfold Ir.Memory.get in HGET.
  simpl in *.
  rewrite list_find_key_set_diffkey in HGET; congruence.
Qed.

Lemma set_get_id:
  forall m bid mb
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = Some mb),
    Ir.Memory.set m bid mb = m.
Proof.
  intros.
  unfold Ir.Memory.set.
  unfold Ir.Memory.get in HGET.
  rewrite list_set_eq.
  destruct m; simpl; reflexivity.
  eapply Ir.Memory.get_In.
  rewrite <- HGET. reflexivity. reflexivity.
  apply Ir.Memory.wf_uniqueid. assumption.
Qed.

Lemma get_unique:
  forall m (HWF:wf m) bid mb res
         (HF:res = list_find_key (blocks m) bid)
         (HGET:Some mb = get m bid),
    res = (bid, mb)::nil \/ res = nil.
Proof.
  intros.
  assert (List.length res < 2).
  {
    assert (HQ := wf_uniqueid m HWF).
    remember (blocks m) as bs.
    assert (HNODUP: NoDup (list_keys (res))).
    {
      apply lsubseq_NoDup with (l := map fst bs).
      eapply lsubseq_map with (l := bs) (l' := res).
      rewrite HF. eapply lsubseq_filter.
      reflexivity.
      reflexivity.
      assumption.
    }
    eapply list_find_key_NoDup.
    eapply HQ. eassumption.
  }
  destruct res.
  - right. reflexivity.
  - destruct res.
    + assert (forallb (fun x => x.(fst) =? bid) (p::nil) = true).
      { rewrite HF.
        apply filter_forallb. }
      simpl in H0.
      rewrite andb_true_r in H0.
      apply beq_nat_true in H0.
      destruct p.
      simpl in H0. rewrite H0.
      unfold get in HGET.
      rewrite <- HF in HGET.
      simpl in HGET.
      inversion HGET.
      left. reflexivity.
    + simpl in H.
      omega.
Qed.

Lemma get_P0_range_diff:
  forall m mb1 mb2 bid1 bid2
         (HWF:wf m)
         (HGET1:Some mb1 = get m bid1)
         (HALIVE1:MemBlock.alive mb1 = true)
         (HGET2:Some mb2 = get m bid2)
         (HALIVE1:MemBlock.alive mb2 = true)
         (HDIFF:bid1 <> bid2),
    MemBlock.P0_range mb1 <> MemBlock.P0_range mb2.
Proof.
  intros.
  inv HWF.
  apply get_In with (blks := blocks m) in HGET1;
    try reflexivity.
  apply get_In with (blks := blocks m) in HGET2;
    try reflexivity.
  assert (List.In (bid1, mb1) (alive_blocks m)).
  { unfold alive_blocks.
    apply List.filter_In.
    split. assumption. simpl. assumption. }
  assert (List.In (bid2, mb2) (alive_blocks m)).
  { unfold alive_blocks.
    apply List.filter_In.
    split. assumption. simpl. assumption. }

  assert (exists l1 l2 l3,
             alive_blocks m = l1++(bid1, mb1)::l2++(bid2, mb2)::l3 \/
             alive_blocks m = l1++(bid2, mb2)::l2++(bid1, mb1)::l3).
  { eapply In_split2. congruence.
    assumption. assumption. }
  destruct H1 as [l1 [l2 [l3 H1]]].
  unfold alive_P_ranges in wf_disjoint0.

  destruct H1.
  { (* .. ++ (bid1 mb1) ++ l2 ++ (bid2, mb) ++ .. *)
    rewrite H1 in wf_disjoint0.
    rewrite List.map_app in wf_disjoint0.
    simpl in wf_disjoint0.
    rewrite List.map_app in wf_disjoint0.
    simpl in wf_disjoint0.
    rewrite List.concat_app in wf_disjoint0.
    rewrite List.concat_cons in wf_disjoint0.
    rewrite List.concat_app in wf_disjoint0.
    rewrite List.concat_cons in wf_disjoint0.
    assert (disjoint_ranges (MemBlock.P_ranges mb1 ++ MemBlock.P_ranges mb2)
           = true).
    { eapply disjoint_lsubseq_disjoint.
      { eapply wf_disjoint0. }
      { rewrite List.app_assoc.
        eapply lsubseq_append with (l5 := MemBlock.P_ranges mb1)
                                   (l7 := MemBlock.P_ranges mb2).
        { eapply lsubseq_append2. eapply lsubseq_refl. }
        { eapply lsubseq_append2. rewrite <- List.app_nil_r.
          eapply lsubseq_append with (l7 := []).
          apply lsubseq_refl. constructor. }
      }
    }
    assert (disjoint_ranges ([MemBlock.P0_range mb1] ++
                             [MemBlock.P0_range mb2]) = true).
    { eapply disjoint_lsubseq_disjoint.
      { eapply H2. }
      { eapply lsubseq_append.
        { simpl. apply MemBlock.P_P0_range_lsubseq.
          eapply wf_blocks0. eassumption. }
        { simpl. apply MemBlock.P_P0_range_lsubseq.
          eapply wf_blocks0. eassumption. }
      }
    }
    intros HEQ. rewrite HEQ in H3.
    rewrite disjoint_ranges_app_false in H3. congruence.
    { congruence. }
    { apply Ir.MemBlock.P0_range_no_empty_range. eapply wf_blocks0. eassumption. }
  }
  { (* .. ++ (bid2 mb2) ++ l2 ++ (bid1, m1) ++ .. *)
    rewrite H1 in wf_disjoint0.
    rewrite List.map_app in wf_disjoint0.
    simpl in wf_disjoint0.
    rewrite List.map_app in wf_disjoint0.
    simpl in wf_disjoint0.
    rewrite List.concat_app in wf_disjoint0.
    rewrite List.concat_cons in wf_disjoint0.
    rewrite List.concat_app in wf_disjoint0.
    rewrite List.concat_cons in wf_disjoint0.
    assert (disjoint_ranges (MemBlock.P_ranges mb2 ++ MemBlock.P_ranges mb1)
           = true).
    { eapply disjoint_lsubseq_disjoint.
      { eapply wf_disjoint0. }
      { rewrite List.app_assoc.
        eapply lsubseq_append with (l5 := MemBlock.P_ranges mb2)
                                   (l7 := MemBlock.P_ranges mb1).
        { eapply lsubseq_append2. eapply lsubseq_refl. }
        { eapply lsubseq_append2. rewrite <- List.app_nil_r.
          eapply lsubseq_append with (l7 := []).
          apply lsubseq_refl. constructor. }
      }
    }
    assert (disjoint_ranges ([MemBlock.P0_range mb2] ++
                             [MemBlock.P0_range mb1]) = true).
    { eapply disjoint_lsubseq_disjoint.
      { eapply H2. }
      { eapply lsubseq_append.
        { simpl. apply MemBlock.P_P0_range_lsubseq.
          eapply wf_blocks0. eassumption. }
        { simpl. apply MemBlock.P_P0_range_lsubseq.
          eapply wf_blocks0. eassumption. }
      }
    }
    intros HEQ. rewrite HEQ in H3.
    rewrite disjoint_ranges_app_false in H3. congruence.
    { congruence. }
    { apply Ir.MemBlock.P0_range_no_empty_range. eapply wf_blocks0. eassumption. }
  }
Qed.  

Lemma alive_P0_ranges_P0_range_In:
  forall m mb bid
         (HGET:Some mb = Ir.Memory.get m bid)
         (HALIVE:Ir.MemBlock.alive mb = true)
         (HWF:Ir.Memory.wf m),
    List.In (Ir.MemBlock.P0_range mb) (Ir.Memory.alive_P0_ranges m).
Proof.
  intros.
  unfold Ir.Memory.alive_P0_ranges.
  assert (List.In (bid, mb) (Ir.Memory.alive_blocks m)).
  { unfold Ir.Memory.alive_blocks.
    eapply List.filter_In.
    split. eapply Ir.Memory.get_In.  eassumption.
    reflexivity. simpl. assumption. }
  eapply map_In. eassumption. reflexivity.
Qed.

Lemma blocks_get:
  forall m (HWF:wf m) bs b
         (HBS:bs = blocks m)
         (HIN:List.In b bs),
    get m b.(fst) = Some b.(snd).
Proof.
  intros.
  destruct b as [bid mb].
  remember (list_find_key (blocks m) bid) as fres.
  assert (List.In (bid, mb) fres).
  { rewrite Heqfres.
    unfold list_find_key.
    rewrite filter_In.
    split. rewrite <- HBS. assumption.
    simpl. symmetry. apply beq_nat_refl. }
  remember (get m bid) as r.
  destruct r.
  - assert (fres = (bid, t0)::nil \/ fres = nil).
    { apply get_unique with (m := m).
      assumption.
      assumption.
      assumption. }
    destruct fres.
    + inversion H.
    + destruct H0.
      * inversion H0.
        rewrite H3 in H.
        inversion H.
        rewrite H2 in H1. inversion H1. rewrite H5 in *.
        simpl. congruence.
        inversion H1.
      * inversion H0.
  - unfold get in Heqr.
    rewrite <- Heqfres in Heqr.
    destruct fres. inversion H. inversion Heqr.
Qed.

Lemma get_fresh_bid:
  forall m (HWF:wf m) mb l
         (HGET:get m l = Some mb),
    l < m.(fresh_bid).
Proof.
  intros.
  inversion HWF.
  symmetry in HGET.
  apply get_In with (blks := m.(blocks)) in HGET; try reflexivity.
  rewrite forallb_forall in wf_newid0.
  apply list_keys_In in HGET.
  apply wf_newid0 in HGET.
  rewrite PeanoNat.Nat.ltb_lt in HGET.
  assumption.
Qed.

Lemma get_new:
  forall m m' l blkty nsz a c P l0
         (HWF:Ir.Memory.wf m)
         (HNEW:(m', l) = Ir.Memory.new m blkty nsz a c P)
         (HDISJ:Ir.Memory.allocatable m (List.map (fun addr => (addr, nsz)) P) = true)
         (HSZ2:nsz > 0)
         (HMBWF:forall begt, Ir.MemBlock.wf (Ir.MemBlock.mk (Ir.heap) (begt, None) nsz
                                                            (Ir.SYSALIGN) c P))
         (HL0:l0 < Ir.Memory.fresh_bid m),
    Ir.Memory.get m' l0 = Ir.Memory.get m l0.
Proof.
  intros.
  unfold Ir.Memory.new in HNEW.
  inv HNEW.
  unfold Ir.Memory.get. simpl.
  apply PeanoNat.Nat.lt_neq in HL0.
  apply not_eq_sym in HL0.
  rewrite <- PeanoNat.Nat.eqb_neq in HL0.
  rewrite HL0. reflexivity.
Qed.

Lemma get_set_diff2:
  forall m bid mb' m' bid'
         (HWF:Ir.Memory.wf m)
         (HWF':Ir.Memory.wf m')
         (HGET:Ir.Memory.get m bid = None)
         (HSET:m' = Ir.Memory.set m bid' mb')
         (HDIFF:bid <> bid'),
    Ir.Memory.get m' bid = None.
Proof.
  intros.
  unfold Ir.Memory.get.
  symmetry in HGET.
  rewrite HSET.
  unfold Ir.Memory.set.
  simpl. rewrite list_find_key_set_diffkey.
  unfold Ir.Memory.get in HGET. congruence.
  congruence.
Qed.

Lemma alive_P_ranges_alive_lsubseq:
  forall m mb l (HGET:Some mb = get m l)
    (HALIVE:Ir.MemBlock.alive mb = true),
          lsubseq (alive_P_ranges m) (MemBlock.P_ranges mb).
Proof.
  intros.
  unfold alive_P_ranges.
  assert (MemBlock.P_ranges mb =
          concat (map (fun b => MemBlock.P_ranges (snd b))
              (filter (fun xb => MemBlock.alive (snd xb)) [(l, mb)]))).
  { simpl. rewrite HALIVE. simpl. rewrite app_nil_r. reflexivity. }
  rewrite H.
  apply lsubseq_concat.
  unfold alive_blocks.
  eapply lsubseq_map; try reflexivity.
  eapply lsubseq_filter2; try reflexivity.
  rewrite lsubseq_In2.
  eapply get_In in HGET; try reflexivity. assumption.
Qed.

Lemma get_new_c_poison:
  forall m m' l nsz P mb
     (HNEW:(m', l) =
           Ir.Memory.new m Ir.heap nsz Ir.SYSALIGN (repeat Ir.Byte.poison nsz) P)
     (HGET:Some mb = Ir.Memory.get m' l),
    Ir.MemBlock.c mb = repeat Ir.Byte.poison nsz.
Proof.
  intros.
  unfold Ir.Memory.new in HNEW.
  inv HNEW.
  unfold Ir.Memory.get in HGET.
  simpl in HGET. rewrite Nat.eqb_refl in HGET. inv HGET.
  simpl. reflexivity.
Qed.




(**********************************************
      Preservation of wellformedness,
      and a few lemmas that use it
 **********************************************)

Lemma disjoint_range_lifetime_to_range_inv:
  forall mb1 l1 mb2 l2 m
         (HWF:wf m)
         (HGET1:Some mb1 = get m l1)
         (HGET2:Some mb2 = get m l2)
         (HOVERLAP:
            disjoint_range (MemBlock.lifetime_to_range (S (mt m)) mb1)
                           (MemBlock.lifetime_to_range (S (mt m)) mb2) = false),
    disjoint_range (MemBlock.lifetime_to_range (mt m) mb1)
                   (MemBlock.lifetime_to_range (mt m) mb2) = false.
Proof.
  intros.
  inv HWF.
  assert (HGET1' := HGET1).
  eapply get_In in HGET1; try reflexivity.
  eapply get_In in HGET1'; try reflexivity.
  assert (HGET2' := HGET2).
  eapply get_In in HGET2; try reflexivity.
  eapply get_In in HGET2'; try reflexivity.
  apply wf_blocktime_beg0 in HGET1.
  apply wf_blocktime_beg0 in HGET2.
  unfold MemBlock.lifetime_to_range in HOVERLAP.
  unfold disjoint_range in HOVERLAP.
  rewrite orb_false_iff in HOVERLAP.
  destruct HOVERLAP.
  destruct (snd (MemBlock.r mb1)) eqn:HR1.
  { exploit wf_blocktime_end0.
    eapply HGET1'. rewrite HR1. reflexivity. intros HH1.
    destruct (snd (MemBlock.r mb2)) eqn:HR2.
    { exploit wf_blocktime_end0.
      eapply HGET2'. rewrite HR2. reflexivity. intros HH2.
      unfold disjoint_range.
      unfold MemBlock.lifetime_to_range.
      rewrite HR1, HR2. rewrite H, H0. reflexivity. }
    { unfold disjoint_range.
      unfold MemBlock.lifetime_to_range.
      rewrite HR1, HR2. rewrite H.
      assert (fst (MemBlock.r mb2) + (mt m - fst (MemBlock.r mb2)) > fst (MemBlock.r mb1)).
      { rewrite Nat.leb_gt in H0. omega. }
      apply gt_not_le in H1.
      rewrite <- Nat.leb_nle in H1. rewrite H1. reflexivity.
    }
  }
  {
    destruct (snd (MemBlock.r mb2)) eqn:HR2.
    { exploit wf_blocktime_end0.
      eapply HGET2'. rewrite HR2. reflexivity. intros HH2.
      unfold disjoint_range.
      unfold MemBlock.lifetime_to_range.
      rewrite HR1, HR2.
      rewrite H0.
      assert (fst (MemBlock.r mb1) + (mt m - fst (MemBlock.r mb1)) > fst (MemBlock.r mb2)).
      { rewrite Nat.leb_gt in H. omega. }
      apply gt_not_le in H1. rewrite <- Nat.leb_nle in H1. rewrite H1. reflexivity. }
    { unfold disjoint_range.
      unfold MemBlock.lifetime_to_range.
      rewrite HR1, HR2.
      assert (fst (MemBlock.r mb2) + (mt m - fst (MemBlock.r mb2)) > fst (MemBlock.r mb1)).
      { rewrite Nat.leb_gt in H0. omega. }
      apply gt_not_le in H1.
      rewrite <- Nat.leb_nle in H1. rewrite H1.
      assert (fst (MemBlock.r mb1) + (mt m - fst (MemBlock.r mb1)) > fst (MemBlock.r mb2)).
      { rewrite Nat.leb_gt in H. omega. }
      apply gt_not_le in H2. rewrite <- Nat.leb_nle in H2. rewrite H2. reflexivity.
    }
  }
Qed.

Lemma disjoint_range_lifetime_to_range_freed_inv:
  forall mb1 l1 mb2 l2 m mb1'
         (HWF:wf m)
         (HGET1:Some mb1 = get m l1)
         (HGET2:Some mb2 = get m l2)
         (HFREE:MemBlock.set_lifetime_end mb1 (mt m) = Some mb1')
         (HOVERLAP:
            disjoint_range (MemBlock.lifetime_to_range (S (mt m)) mb1')
                           (MemBlock.lifetime_to_range (S (mt m)) mb2) = false),
    disjoint_range (MemBlock.lifetime_to_range (mt m) mb1)
                   (MemBlock.lifetime_to_range (mt m) mb2) = false.
Proof.
  intros.
  unfold MemBlock.set_lifetime_end in HFREE.
  des_ifs.
  unfold MemBlock.lifetime_to_range in *.
  simpl in *.
  (* okay, we should get wellformedness of lifetime as well. *)
  inv HWF.
  dup HGET1. eapply get_In in HGET0; try reflexivity.
    eapply get_In in HGET1; try reflexivity.
    eapply wf_blocktime_beg0 in HGET0.
  dup HGET2. eapply get_In in HGET3; try reflexivity.
    eapply get_In in HGET2; try reflexivity.
    eapply wf_blocktime_beg0 in HGET2.
  (* mb1 was alive. *)
  unfold MemBlock.alive in Heq.

  unfold disjoint_range in *.
  rewrite orb_false_iff in *.
  destruct HOVERLAP.
  repeat (rewrite Nat.leb_gt in *).
  des_ifs.
  split. omega. omega.
Qed.

Lemma new_wf:
  forall m (HWF:wf m) t n a c P m' mb
         (HWF0: forall begt, MemBlock.wf (MemBlock.mk t (begt, None) n a c P))
         (HDISJ:allocatable m (List.map (fun x => (x, n)) P) = true)
         (HNEW:(m', mb) = new m t n a c P),
    wf m'.
Proof.
  intros.
  unfold new in HNEW.
  inversion HNEW. clear HNEW.
  inversion HWF.
  split; simpl.
  - (* blocks' wf *)
    intros. destruct HAS.
    + inversion H. clear H. apply HWF0.
    + eapply wf_blocks0. eassumption.
  - (* no block id dup *)
    rewrite NoDup_cons_iff. split; try assumption.
    intros HIN.
    rewrite forallb_forall in wf_newid0.
    apply wf_newid0 in HIN.
    rewrite Nat.ltb_lt in HIN. omega.
  - (* fresh_bid is larger than any other key *)
    assert (fresh_bid m <? S (fresh_bid m) = true).
    { rewrite Nat.ltb_lt. omega. }
    rewrite H. simpl.
    rewrite forallb_forall. rewrite <- Forall_forall.
    rewrite forallb_forall in wf_newid0. rewrite <- Forall_forall in wf_newid0.
    apply Forall_impl with (P := (fun x:nat => (x <? fresh_bid m) = true)).
    intros.
    rewrite Nat.ltb_lt in H2.
    rewrite Nat.ltb_lt. omega.
    assumption.
  - (* disjointness of fresh blocks *)
    unfold allocatable in HDISJ.
    apply disjoint_lsubseq_disjoint
      with (rs := map (fun x : nat => (x, n)) P ++ alive_P_ranges m).
    assumption.
    assert (alive_P_ranges m' = (List.map (fun addr => (addr, n)) P)
                                  ++ alive_P_ranges m).
    { unfold alive_P_ranges. unfold MemBlock.P_ranges.
      rewrite H0. simpl.
      unfold alive_blocks. reflexivity.
    }
    rewrite <- H. rewrite <- H0. apply lsubseq_refl.
  - (* disjointness, general version *)
    intros.
    destruct (l1 =? fresh_bid m) eqn:HEQ1;
      destruct (l2 =? fresh_bid m) eqn:HEQ2.
    { rewrite PeanoNat.Nat.eqb_eq in *. des_ifs. }
    { rewrite PeanoNat.Nat.eqb_eq in HEQ1. subst l1.
      (* mb1 is the new block. *)
      unfold get in HGET1. simpl in HGET1.
      rewrite Nat.eqb_refl in HGET1. simpl in HGET1.
      inv HGET1.
      (* mb2 is the old block. *)
      assert (HGET2':Some mb2 = get m l2).
      { rewrite HGET2. unfold get. simpl.
        rewrite Nat.eqb_sym in HEQ2. rewrite HEQ2. reflexivity. }
      clear HGET2.
      (* we're going to use lsubseq relation from HDISJ. *)
      unfold MemBlock.lifetime_to_range in HOVERLAP.
      simpl in HOVERLAP.
      unfold allocatable in HDISJ.
      unfold MemBlock.P_ranges at 1. simpl.
      eapply disjoint_lsubseq_disjoint. eapply HDISJ.
      (* okay.. let's show the lsubseq relation. *)
      eapply lsubseq_append.
      { apply lsubseq_refl. }
      { eapply alive_P_ranges_alive_lsubseq.
        eassumption.
        eapply get_In in HGET2'; try reflexivity.
        (* is it already free, or .. ?*)
        destruct (snd (MemBlock.r mb2)) eqn:HR.
        { (* yes, it was freed! *)
          eapply wf_blocktime_end0 in HGET2'.
          2: rewrite HR. 2: reflexivity.
          unfold disjoint_range in HOVERLAP.
          rewrite orb_false_iff in HOVERLAP.
          repeat (rewrite Nat.leb_gt in HOVERLAP).
          destruct HOVERLAP. omega.
        }
        { (* nop. *)
          unfold MemBlock.alive. des_ifs. }
      }
    }
    { rewrite PeanoNat.Nat.eqb_eq in HEQ2. subst l2.
      (* mb2 is the new block. *)
      unfold get in HGET2. simpl in HGET2.
      rewrite Nat.eqb_refl in HGET2. simpl in HGET2.
      inv HGET2.
      (* mb1 is the old block. *)
      assert (HGET1':Some mb1 = get m l1).
      { rewrite HGET1. unfold get. simpl.
        rewrite Nat.eqb_sym in HEQ1. rewrite HEQ1. reflexivity. }
      clear HGET1.
      (* we're going to use lsubseq relation from HDISJ. *)
      unfold MemBlock.lifetime_to_range in HOVERLAP.
      simpl in HOVERLAP.
      unfold allocatable in HDISJ.
      unfold MemBlock.P_ranges at 2. simpl.
      rewrite disjoint_ranges_app_comm.
      eapply disjoint_lsubseq_disjoint. eapply HDISJ.
      (* okay.. let's show the lsubseq relation. *)
      eapply lsubseq_append.
      { apply lsubseq_refl. }
      { eapply alive_P_ranges_alive_lsubseq.
        eassumption.
        eapply get_In in HGET1'; try reflexivity.
        (* is it already free, or .. ?*)
        destruct (snd (MemBlock.r mb1)) eqn:HR.
        { (* yes, it was freed! *)
          eapply wf_blocktime_end0 in HGET1'.
          2: rewrite HR. 2: reflexivity.
          unfold disjoint_range in HOVERLAP.
          rewrite orb_false_iff in HOVERLAP.
          repeat (rewrite Nat.leb_gt in HOVERLAP).
          destruct HOVERLAP. omega.
        }
        { (* nop. *)
          unfold MemBlock.alive. des_ifs. }
      }
    }
    { (* both are old. *)
      assert (HGET1':Some mb1 = get m l1).
      { rewrite HGET1. unfold get. simpl.
        rewrite Nat.eqb_sym in HEQ1. rewrite HEQ1. reflexivity. }
      clear HGET1.
      assert (HGET2':Some mb2 = get m l2).
      { rewrite HGET2. unfold get. simpl.
        rewrite Nat.eqb_sym in HEQ2. rewrite HEQ2. reflexivity. }
      clear HGET2.
      eapply wf_disjoint3; try eassumption.
      (* lifetime_to_range.. *)
      dup HGET1'.
      eapply get_In in HGET1'0; try reflexivity.
        eapply wf_blocktime_beg0 in HGET1'0.
      dup HGET2'.
      eapply get_In in HGET2'0; try reflexivity.
        eapply wf_blocktime_beg0 in HGET2'0.
      eapply disjoint_range_lifetime_to_range_inv;try eassumption.
    }
  - (*wf blocktime beg *)
    intros.
    destruct HAS.
    + inversion H. simpl. omega.
    + apply Nat.lt_trans with (m := mt m).
      eapply wf_blocktime_beg0. eapply H. omega.
  - (* wf blocktime end *)
    intros.
    destruct HAS.
    + inv H. inv HEND.
    + exploit wf_blocktime_end0; try eassumption.
      intros HH. omega.
Qed.

Lemma incr_time_wf:
  forall m (HWF:wf m) m'
         (HFREE:m' = incr_time m),
    wf m'.
Proof.
  intros.
  unfold incr_time in HFREE. dup HWF.
  destruct HWF.
  split; try (rewrite HFREE; simpl; assumption).
  { (* disointness, general *)
    rewrite HFREE.
    simpl.
    intros.
    eapply disjoint_range_lifetime_to_range_inv in HOVERLAP; try eassumption.
    eapply wf_disjoint3. eapply HGET1. eapply HGET2. assumption.
      assumption.
  }
  { (* wf_blocktime_beg *)
    rewrite HFREE. simpl. intros.
    apply lt_trans with (m := mt m).
    eapply wf_blocktime_beg0; eassumption.
    omega.
  }
  { (* wf_blocktime_end *)
    rewrite HFREE. simpl. intros.
    exploit wf_blocktime_end0; try eassumption. intros HH. omega.
  }
Qed.

Lemma free_wf:
  forall m (HWF:wf m) bid m'
         (HFREE:Some m' = free m bid),
    wf m'.
Proof.
  intros.
  unfold free in HFREE.
  destruct (get m bid) as [blk | ] eqn:Hget; try (inversion HFREE; fail).
  destruct (MemBlock.bt blk) eqn:Hbt; try (inversion HFREE; fail).
  destruct (MemBlock.alive blk) eqn:Halive; try (inversion HFREE; fail).
  destruct (MemBlock.set_lifetime_end blk (mt m)) as [blk' | ] eqn:Hlf;
    try (inversion HFREE; fail).
  assert (HMBWF:MemBlock.wf blk).
  { inversion HWF.
    eapply wf_blocks0. apply get_In with (m := m). rewrite Hget. reflexivity.
    reflexivity. }
  assert (HMBWF':MemBlock.wf blk').
  { inversion HMBWF.
    unfold MemBlock.set_lifetime_end in Hlf.
    unfold MemBlock.alive in Hlf.
    destruct (MemBlock.r blk) as [tfst tsnd] eqn:Hrblk.
    destruct tsnd as [tsnd | ].
    simpl in Hlf. inversion Hlf.
    simpl in Hlf. inversion Hlf.
    split; try (simpl; assumption; fail).
    - simpl. inversion HWF.
      intros.
      inversion FREED.
      replace tfst with (fst (MemBlock.r blk)).
      eapply wf_blocktime_beg0. eapply get_In. rewrite <- Hget. reflexivity. reflexivity.
      rewrite Hrblk. reflexivity.
  }
  inversion HFREE.
  unfold incr_time.
  inversion HWF.
  split.
  - intros. simpl in HAS.
    destruct (Nat.eqb i bid) eqn:Hbid.
    + rewrite Nat.eqb_eq in Hbid.
      assert (p = blk').
      { eapply list_set_NoDup_In_unique with (key := i).
        rewrite <- Hbid in HAS. eapply HAS.
        assumption. }
      rewrite H. assumption.
    + rewrite Nat.eqb_neq in Hbid.
      apply wf_blocks0 with (i := i). 
      apply list_set_In_not_In in HAS. assumption. assumption.
  - simpl. erewrite list_set_keys_eq. eassumption. reflexivity.
  - simpl. erewrite list_set_keys_eq. eassumption. reflexivity.
  - assert (MemBlock.P blk = MemBlock.P blk').
    { unfold MemBlock.set_lifetime_end in Hlf.
      destruct (MemBlock.alive blk).
      inversion Hlf. reflexivity.
      inversion Halive. }
    assert (HLSS:lsubseq (alive_P_ranges m) (alive_P_ranges (set m bid blk'))).
    { unfold set.
      assert (HINKEY:List.In bid (list_keys (blocks m))).
      { eapply get_In_key. rewrite Hget. reflexivity. reflexivity. }
      remember (list_set (blocks m) bid blk') as blocks'.
      assert (HDEC := list_set_decompose (blocks m) blocks'
                                         bid blk' wf_uniqueid0 HINKEY Heqblocks').
      destruct HDEC as [l1 [l2 [mb [HDEC1 [HDEC2 [HDEC3 HDEC4]]]]]].
      assert (HMB: mb = blk).
      { (* from get m bid = Some blk, and List.In (bid, mb) (l1++(bid,mb)::l2). *)
        assert (HIN:List.In (bid, blk) (blocks m)).
        { eapply get_In. rewrite <- Hget. reflexivity. reflexivity. }
        rewrite HDEC1 in HIN.
        apply in_app_or in HIN.
        destruct HIN as [HIN | HIN].
        - eapply list_keys_In_False in HDEC3. omega. eapply HIN.
        - simpl in HIN.
          destruct HIN as [HIN | HIN]. congruence.
          eapply list_keys_In_False in HDEC4. omega. eapply HIN.
      }
      rewrite HMB in *. clear HMB.
      unfold alive_P_ranges.
      unfold alive_blocks.
      rewrite HDEC1.
      rewrite HDEC2.
      simpl.
      rewrite filter_app.
      rewrite filter_app.
      simpl.
      rewrite map_app.
      rewrite map_app.
      (* show that  MemBlock.alive mb is true, but
         MemBlock.alive blk' is false. *)
      rewrite Halive.
      unfold MemBlock.set_lifetime_end in Hlf.
      rewrite Halive in Hlf. inversion Hlf as [Hlf'].
      simpl.
      rewrite concat_app. rewrite concat_app.
      apply lsubseq_append.
      - apply lsubseq_refl.
      - simpl. apply lsubseq_append2. apply lsubseq_refl.
   }
    eapply disjoint_lsubseq_disjoint.
    eapply wf_disjoint0.
    assumption.
  - (* disjointness,general *)
    simpl. intros.
    destruct (l1 =? bid) eqn:H1.
    { (* the freedblock. *)
      rewrite PeanoNat.Nat.eqb_eq in H1. subst l1.
      unfold get in HGET1. unfold set in HGET1. simpl in HGET1.
      rewrite list_find_key_set_samekey in HGET1.
      inv HGET1.
      (* l2 is not the block. *)
      assert (HGET2': Some mb2 = get m l2).
      { unfold get in HGET2. unfold set in HGET2. simpl in HGET2.
        rewrite list_find_key_set_diffkey in HGET2; try congruence.
        unfold get. assumption. }
      clear HGET2.
      (* okay, bid and l2 was already disjoint. *)
      (* MemBlock.set_lifetime_end blk (mt m) = Some blk' *)
      eapply disjoint_range_lifetime_to_range_freed_inv in HOVERLAP.
      3: rewrite Hget; reflexivity.
      3: eapply HGET2'.
      assert (HP:MemBlock.P_ranges blk' = MemBlock.P_ranges blk).
      { unfold MemBlock.P_ranges.
        unfold MemBlock.set_lifetime_end in Hlf.
        des_ifs. }
      rewrite HP.
      eapply wf_disjoint3.
      { rewrite Hget. reflexivity. }
      { eapply HGET2'. }
      { omega. }
      { assumption. }
      { assumption. }
      { assumption. }
      { assumption. }
      { symmetry in Hget. eapply get_In in Hget.
        eapply list_keys_In in Hget. eassumption. reflexivity. }
    }
    { (* no, it was unrelated block *)
      assert (HGET1': Some mb1 = get m l1).
      { rewrite HGET1. unfold get. unfold set. simpl.
        rewrite list_find_key_set_diffkey. reflexivity.
        rewrite PeanoNat.Nat.eqb_neq in H1. assumption. }
      clear HGET1.

      destruct (l2 =? bid) eqn:H2.
      { (* l2 is the freed block. *)
        rewrite PeanoNat.Nat.eqb_eq in H2. subst l2.
        unfold get in HGET2. unfold set in HGET2. simpl in HGET2.
        rewrite list_find_key_set_samekey in HGET2.
        inv HGET2.
        (* okay, bid and l2 was already disjoint. *)
        (* MemBlock.set_lifetime_end blk (mt m) = Some blk' *)
        rewrite disjoint_range_symm in HOVERLAP.
        eapply disjoint_range_lifetime_to_range_freed_inv in HOVERLAP.
        3: rewrite Hget; reflexivity.
        3: eapply HGET1'.
        assert (HP:MemBlock.P_ranges blk' = MemBlock.P_ranges blk).
        { unfold MemBlock.P_ranges.
          unfold MemBlock.set_lifetime_end in Hlf.
          des_ifs. }
        rewrite HP.
        eapply wf_disjoint3.
        { rewrite HGET1'. reflexivity. }
        { rewrite Hget. reflexivity. }
        { omega. }
        { rewrite disjoint_range_symm. assumption. }
        { assumption. }
        { assumption. }
        { assumption. }
        { symmetry in Hget. eapply get_In in Hget.
          eapply list_keys_In in Hget. eassumption. reflexivity. }
      }
      {
        assert (HGET2': Some mb2 = get m l2).
        { rewrite HGET2. unfold get. unfold set. simpl.
          rewrite list_find_key_set_diffkey. reflexivity.
          rewrite PeanoNat.Nat.eqb_neq in H2. assumption. }
        clear HGET2.
        eapply wf_disjoint3; try eassumption.
        eapply disjoint_range_lifetime_to_range_inv in HOVERLAP;
          eassumption.
      }
    }
  - (* block lifetime beg *)
    simpl. intros.
    destruct (i =? bid) eqn:Hbid.
    { rewrite Nat.eqb_eq in Hbid.
      rewrite Hbid in HAS.
      assert (p = blk').
      { eapply list_set_NoDup_In_unique.
        eassumption. assumption. }
      rewrite H.
      assert (HR:fst (MemBlock.r blk') = fst (MemBlock.r blk)).
      { unfold MemBlock.set_lifetime_end in Hlf.
        destruct (MemBlock.alive blk).
        inversion Hlf. simpl. reflexivity. inversion Hlf. }
      rewrite HR.
      apply Nat.lt_trans with (m := mt m).
      - eapply wf_blocktime_beg0. eapply get_In. rewrite <- Hget. reflexivity.
        reflexivity.
      - omega.
    }
    { apply Nat.lt_trans with (m := mt m).
      assert (In (i, p) (blocks m)).
      { eapply list_set_In_not_In. eapply HAS. rewrite Nat.eqb_neq in Hbid.
        assumption. }
      eapply wf_blocktime_beg0. eassumption. omega.
    }
  - (* block lifetime end *)
    simpl. intros.
    destruct (i =? bid) eqn:Hbid.
    { rewrite Nat.eqb_eq in Hbid. subst i.
      assert (p = blk').
      { eapply list_set_NoDup_In_unique.
        eassumption. assumption. }
      subst p.
      assert (HR:fst (MemBlock.r blk') = fst (MemBlock.r blk)).
      { unfold MemBlock.set_lifetime_end in Hlf.
        destruct (MemBlock.alive blk).
        inversion Hlf. simpl. reflexivity. inversion Hlf. }
      rewrite HR in *.
      unfold MemBlock.set_lifetime_end in Hlf.
      rewrite Halive in Hlf.
      inversion Hlf. rewrite <- H1 in HEND. simpl in HEND. inversion HEND.
      subst e.
      symmetry in Hget. eapply get_In in Hget; try reflexivity.
      unfold MemBlock.alive in Halive.
      des_ifs.
      eapply wf_blocktime_beg0 in Hget. omega.
    }
    { 
      assert (In (i, p) (blocks m)).
      { eapply list_set_In_not_In. eapply HAS. rewrite Nat.eqb_neq in Hbid.
        assumption. }
      symmetry in Hget. eapply get_In in Hget;try reflexivity.
      eapply wf_blocktime_end0 in H.
      2: eassumption.
      omega.
    }
Qed.

(* Wellformedness, inversed direction - when a new block is added. *)
Lemma wf_newblk_inv:
  forall mt blocks newblk calltime fresh_cid
         (HWF: wf (mk mt (newblk::blocks) calltime fresh_cid)),
    wf (mk mt blocks calltime fresh_cid).
Proof.
  intros. dup HWF.
  destruct HWF.
  split.
  - intros.
    apply wf_blocks0 with (i := i).
    simpl. simpl in HAS. right. assumption.
  - simpl. simpl in wf_uniqueid0.
    inversion wf_uniqueid0. assumption.
  - simpl in *. rewrite andb_true_iff in wf_newid0.
    destruct wf_newid0. assumption.
  - unfold alive_P_ranges in *.
    unfold alive_blocks in *.
    simpl in *.
    destruct (MemBlock.alive (snd newblk)) eqn:HALIVE.
    + simpl in wf_disjoint0.
      apply disjoint_ranges_append in wf_disjoint0.
      destruct wf_disjoint0.
      assumption.
    + assumption.
  - simpl in *. intros.
    eapply wf_disjoint3 with (l1 := l1) (l2 := l2); try assumption.
    { eapply get_In in HGET1; try reflexivity.
      apply In_get. assumption.
      simpl in *. right. assumption. }
    { eapply get_In in HGET2; try reflexivity.
      apply In_get. assumption.
      simpl in *. right. assumption. }
  - simpl in *. intros.
    eapply wf_blocktime_beg0. right. eassumption.
  - simpl in *. intros.
    eapply wf_blocktime_end0. right. eassumption. assumption.
Qed.

Lemma get_free:
  forall m m' l l0 blk blk'
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l)
         (HGET: Some blk  = Ir.Memory.get m l0)
         (HGET':Some blk' = Ir.Memory.get m' l0),
    Ir.MemBlock.addr blk = Ir.MemBlock.addr blk'.
Proof.
  intros.
  assert (Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (PeanoNat.Nat.eqb l l0) eqn:HLEQ.
  { rewrite PeanoNat.Nat.eqb_eq in HLEQ.
    subst l.
    rewrite Ir.Memory.get_set_id with (m := Ir.Memory.incr_time m)
      (mb := blk)
      (mb' := t1) (m' := Ir.Memory.set (Ir.Memory.incr_time m) l0 t1) in HGET';
      try congruence.
    { unfold Ir.MemBlock.set_lifetime_end in Heq2.
      destruct (Ir.MemBlock.alive t0).
      { inv Heq2. inv HGET'. rewrite Heq in HGET.
        inv HGET. unfold Ir.MemBlock.addr.
        simpl. reflexivity. }
      { congruence. }
    }
    { apply Ir.Memory.incr_time_wf with (m := m). assumption.
      reflexivity. }
    { unfold Ir.Memory.get in *.
      unfold Ir.Memory.incr_time. simpl. congruence.
    }
  }
  { rewrite PeanoNat.Nat.eqb_neq in HLEQ.
    rewrite get_set_diff with (m := Ir.Memory.incr_time m)
                              (mb' := t1) (mb := blk) (bid' := l)
      in HGET'; try assumption; try congruence.
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { rewrite Ir.Memory.get_incr_time_id. congruence. }
  }
Qed.

Lemma get_free_some:
  forall m m' l l0 blk
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l0)
         (HGET:Ir.Memory.get m l = Some blk),
    exists blk', Ir.Memory.get m' l = Some blk'.
Proof.
  intros.
  assert (HFREEWF:Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  unfold Ir.MemBlock.set_lifetime_end in Heq2.
  des_ifs.
  symmetry in HGET.
  (* apply Ir.Memory.get_In with (blks := Ir.Memory.blocks m) in HGET. *)
  destruct (Nat.eqb l0 l) eqn:HL.
  { rewrite PeanoNat.Nat.eqb_eq in HL.
    subst l0.
    erewrite Ir.Memory.get_set_id with (bid := l) (m := Ir.Memory.incr_time m).
    { eexists. reflexivity. }
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { rewrite Ir.Memory.get_incr_time_id. symmetry in HGET. eassumption. }
    { reflexivity. }
  }
  { rewrite PeanoNat.Nat.eqb_neq in HL.
    erewrite Ir.Memory.get_set_diff with (bid := l) (bid' := l0) (m := Ir.Memory.incr_time m).
    { eexists. reflexivity. }
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { rewrite Ir.Memory.get_incr_time_id. symmetry in HGET. eassumption. }
    { reflexivity. }
    { omega. }
  }
Qed.

Lemma get_free_none:
  forall m m' l l0
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l0)
         (HGET:Ir.Memory.get m l = None),
    Ir.Memory.get m' l = None.
Proof.
  intros.
  assert (HFREEWF:Ir.Memory.wf m').
  { eapply Ir.Memory.free_wf. eassumption. eassumption. }
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  unfold Ir.MemBlock.set_lifetime_end in Heq2.
  des_ifs.
  destruct (Nat.eqb l0 l) eqn:HL.
  { rewrite PeanoNat.Nat.eqb_eq in HL.
    subst l0.
    congruence. }
  { rewrite PeanoNat.Nat.eqb_neq in HL.
    erewrite get_set_diff2 with (bid := l) (bid' := l0) (m := Ir.Memory.incr_time m).
    { reflexivity. }
    { eapply Ir.Memory.incr_time_wf. eapply HWF. reflexivity. }
    { eassumption. }
    { rewrite Ir.Memory.get_incr_time_id. eassumption. }
    { reflexivity. }
    { omega. }
  }
Qed.

Lemma get_free_c:
  forall m m' b bid mb mb'
         (HWF:Ir.Memory.wf m)
         (HFREE:Ir.Memory.free m b = Some m')
         (HGET:Some mb = Ir.Memory.get m bid)
         (HGET':Some mb' = Ir.Memory.get m' bid),
    Ir.MemBlock.c mb = Ir.MemBlock.c mb'.
Proof.
  intros.
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (b =? bid) eqn:HEQ.
  { rewrite Nat.eqb_eq in HEQ.
    subst b.
    erewrite Ir.Memory.get_set_id_short in HGET'. inv HGET'.
    unfold Ir.MemBlock.set_lifetime_end in Heq2.
    des_ifs. simpl. congruence.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Ir.Memory.get_incr_time_id. rewrite HGET. ss.
  }
  { rewrite Ir.Memory.get_set_diff_short in HGET'.
    rewrite Ir.Memory.get_incr_time_id in HGET'. congruence.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Nat.eqb_neq in HEQ. congruence.
  }
Qed.

Lemma get_free_some_inv:
  forall (m m' : Ir.Memory.t) (l l0 : Ir.blockid) (blk : Ir.MemBlock.t)
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l0)
         (HGET:Ir.Memory.get m' l = Some blk),
  exists blk' : Ir.MemBlock.t, Ir.Memory.get m l = Some blk'.
Proof.
  intros.
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (l0 =? l) eqn:HEQ.
  { rewrite Nat.eqb_eq in HEQ.
    subst. eexists. eassumption. }
  { erewrite Ir.Memory.get_set_diff_short in HGET.
    rewrite Ir.Memory.get_incr_time_id in HGET.
    eexists. eapply HGET.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Nat.eqb_neq in HEQ. congruence.
  }
Qed.


(**********************************************
      Lemmas&Theorems about inboundness
 **********************************************)

Lemma blocks_alive_blocks_lsubseq:
  forall (m:t),
    lsubseq (blocks m) (alive_blocks m).
Proof.
  intros.
  destruct m.
  unfold alive_blocks.
  simpl.
  apply lsubseq_filter.
Qed.

Lemma alive_P_P0_ranges_lsubseq:
  forall (m:t) (HWF:wf m),
    lsubseq (alive_P_ranges m) (alive_P0_ranges m).
Proof.
  intros.
  unfold alive_P_ranges.
  unfold alive_P0_ranges.
  destruct m eqn:HM.
  unfold alive_blocks.
  simpl.
  generalize dependent m.
  induction blocks0.
  - simpl. intros. constructor.
  - simpl. intros.
    destruct a as [newbid newb].
    simpl.
    destruct (MemBlock.alive newb) eqn:HALIVE.
    + simpl.
      (* Why do I need this?? *)
      assert (forall {X:Type} (p: X) (q:list X), p::q = (p::nil) ++ q).
      { simpl. reflexivity. }
      rewrite H.
      apply lsubseq_append.
      {
        apply MemBlock.P_P0_range_lsubseq.
        apply wf_blocks with (m := m) (i := newbid).
        rewrite HM.
        apply HWF.
        rewrite HM. simpl. left. reflexivity.
      }
      {
        eapply IHblocks0.
        eapply wf_newblk_inv.
        apply HWF.
        reflexivity.
      }
    + eapply IHblocks0.
      eapply wf_newblk_inv.
      apply HWF. reflexivity.
Qed.

Lemma disjoint_range_P0_range:
  forall m bid1 bid2 mb1 mb2
         (HWF:Ir.Memory.wf m)
         (HGET1:Some mb1 = Ir.Memory.get m bid1)
         (HALIVE1:Ir.MemBlock.alive mb1)
         (HGET2:Some mb2 = Ir.Memory.get m bid2)
         (HALIVE2:Ir.MemBlock.alive mb2)
         (HDIFF:bid1 <> bid2),
    disjoint_range (Ir.MemBlock.P0_range mb1)
                   (Ir.MemBlock.P0_range mb2).
Proof.
  intros. dup HWF.
  inv HWF.
  assert (disjoint_ranges (Ir.Memory.alive_P0_ranges m) = true).
  { eapply disjoint_lsubseq_disjoint.
    eapply wf_disjoint0.
    eapply Ir.Memory.alive_P_P0_ranges_lsubseq.
    assumption. }
  assert (Ir.MemBlock.P0_range mb1 <> Ir.MemBlock.P0_range mb2).
  { eapply get_P0_range_diff; try eassumption. }
  assert (List.In (Ir.MemBlock.P0_range mb1) (Ir.Memory.alive_P0_ranges m)).
  { eapply alive_P0_ranges_P0_range_In; try eassumption. }
  assert (List.In (Ir.MemBlock.P0_range mb2) (Ir.Memory.alive_P0_ranges m)).
  { eapply alive_P0_ranges_P0_range_In; try eassumption. }
  eapply disjoint_ranges_In; try assumption.
  eapply H.
  assumption.
  assumption.
Qed.

Lemma alive_blocks_In:
  forall (m:t) bid blk blks
    (HBLK:Some blk = get m bid)
    (HALIVE:MemBlock.alive blk = true)
    (HALIVES:blks = alive_blocks m),
    List.In (bid, blk) blks.
Proof.
  intros.
  unfold alive_blocks in HALIVES.
  rewrite HALIVES.
  rewrite filter_In.
  split.
  - apply get_In with (m := m).
    assumption.
    reflexivity.
  - assumption.
Qed.


(* Lemma: there are at most 2 alive blocks
   which have abs_ofs as inbounds. *)
Lemma inbounds_blocks_atmost_2:
  forall (m:t) abs_ofs l
         (HWF:wf m)
         (HINB:inbounds_blocks m abs_ofs = l),
    List.length l < 3.
Proof.
  intros.
  unfold inbounds_blocks in HINB.
  rewrite <- HINB.
  rewrite <- disjoint_include2_len.
  rewrite disjoint_include_include2.
  eapply disjoint_includes_atmost_2 with (rs := (alive_P0_ranges m)).
  - (* disjoint_ranges (alive_P0_ranges m) is true. *)
    apply disjoint_lsubseq_disjoint with (rs := alive_P_ranges m).
    (* disjoint_ranges (alive_P_ranges m) is true. *)
    apply wf_disjoint. assumption.
    apply alive_P_P0_ranges_lsubseq.
    assumption.
  - reflexivity.
  - apply no_empty_range_lsubseq with (l1 := alive_P_ranges m).
    unfold alive_P_ranges.
    apply no_empty_range_concat.
    intros.
    apply In_map in HIN.
    destruct HIN as [x HIN].
    destruct HIN as [HPSZ HIN].
    apply lsubseq_In with (l1 := blocks m) in HIN .
    + assert (MemBlock.wf x.(snd)).
      { apply wf_blocks with (m := m) (i := x.(fst)).
        assumption.
        destruct x; assumption.
      }
      rewrite <- HPSZ.
      apply MemBlock.wf_poslen. assumption.
    + apply blocks_alive_blocks_lsubseq.
    + apply alive_P_P0_ranges_lsubseq.
      assumption.
  - unfold alive_P0_ranges.
    rewrite map_length. reflexivity.
  - unfold alive_P0_ranges.
    rewrite map_length. reflexivity.
Qed.

Lemma alive_P0_ranges_blocks_len:
  forall (m:t),
    List.length (alive_P0_ranges m) = List.length (alive_blocks m).
Proof.
  intros.
  unfold alive_P0_ranges.
  apply map_length.
Qed.

Lemma inbounds_blocks_lsubseq:
  forall (m:t) abs_ofs l
         (HINB:inbounds_blocks m abs_ofs = l),
    lsubseq m.(blocks) l.
Proof.
  intros.
  unfold inbounds_blocks in HINB.
  apply lsubseq_trans with (l2 := alive_blocks m).
  - apply blocks_alive_blocks_lsubseq.
  - destruct (disjoint_include2 (alive_P0_ranges m) (alive_blocks m) abs_ofs) eqn:Hls.
    assert (lsubseq (alive_P0_ranges m) l0 /\
            lsubseq (alive_blocks m) l1).
    { eapply lsubseq_combine.
      - apply alive_P0_ranges_blocks_len.
      - replace (length l0) with (length (fst (l0, l1))).
        replace (length l1) with (length (snd (l0, l1))).
        rewrite <- Hls.
        apply disjoint_include2_len.
        apply alive_P0_ranges_blocks_len.
        reflexivity. reflexivity.
      - eapply disjoint_include2_lsubseq.
        eassumption.
    }
    destruct H.
    simpl in HINB.
    rewrite HINB in *.
    assumption.
Qed.

(* Lemma: inbounds_blocks ofs is equivalent to
   inbounds_blocks2 [ofs]. *)
Lemma inbounds_blocks_inbounds_blocks2:
  forall (m:t) abs_ofs,
    inbounds_blocks m abs_ofs = inbounds_blocks2 m (abs_ofs::nil).
Proof.
  intros.
  unfold inbounds_blocks.
  unfold inbounds_blocks2.
  simpl. reflexivity.
Qed.
 

(* Lemma: we can generate the result of alive_P0_ranges from alive_blocks. *)
Lemma alive_blocks_P0_ranges:
  forall (m:t),
    List.map (fun mb => MemBlock.P0_range mb.(snd)) (alive_blocks m) =
    alive_P0_ranges m.
Proof.
  intros.
  unfold alive_P0_ranges.
  unfold alive_blocks.
  reflexivity.
Qed.

(* Lemma: the result of inbounds_blocks all satisfies inbounds_abs. *)
Lemma inbounds_blocks_forallb:
  forall (m:t) abs_ofs blks
         (HALL:inbounds_blocks m abs_ofs = blks),
    List.forallb (MemBlock.inbounds_abs abs_ofs)
                 (snd (List.split blks)) = true.
Proof.
  intros.
  unfold inbounds_blocks in HALL.
  remember (alive_P0_ranges m) as ar.
  remember (alive_blocks m) as ab.
  remember (disjoint_include2 ar ab abs_ofs) as res.
  assert (fst res = disjoint_include ar abs_ofs).
  { rewrite Heqres.
    rewrite disjoint_include_include2.
    reflexivity.
    rewrite Heqar. rewrite Heqab.
    apply alive_P0_ranges_blocks_len.
  }
  assert (List.forallb (in_range abs_ofs) (fst res) = true).
  { eapply disjoint_include_inrange.
    eassumption.
  }
  unfold MemBlock.inbounds_abs.
  destruct res as [ranges blks0].
  simpl in HALL.
  rewrite HALL in *.
  clear HALL.
  simpl in H0.
  assert (fst (ranges, blks) = List.map (fun mb => MemBlock.P0_range mb.(snd))
                            (snd (ranges, blks))).
  {
    rewrite Heqres.
    rewrite disjoint_include2_rel. reflexivity.
    rewrite Heqar, Heqab.
    rewrite alive_blocks_P0_ranges. reflexivity.
  }
  simpl in H1.
  assert (ranges = map (fun mb:MemBlock.t => MemBlock.P0_range mb)
                       (snd (split blks))).
  {
    rewrite H1.
    apply split_map_snd.
    reflexivity.
  }
  eapply forallb_map with (l' := ranges).
  eassumption.
  eassumption.
  intros. reflexivity.
Qed.

Lemma inbounds_blocks2_forallb:
  forall (m:t) a abs_ofs blks
         (HALL:inbounds_blocks2 m (a::abs_ofs) = blks),
    List.forallb (MemBlock.inbounds_abs a) (snd (List.split blks)) = true.
Proof.
  intros.
  unfold inbounds_blocks2 in HALL.
  simpl in HALL.
  remember (disjoint_include2 (alive_P0_ranges m) (alive_blocks m) a) as init.
  destruct init as [init_rs init_blks].
  remember (fold_left
              (fun (blks_and_ranges : list (nat * nat) * list (blockid * MemBlock.t))
                 (abs_ofs : nat) =>
               disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs)
              abs_ofs (init_rs, init_blks)) as res.
  assert (HLSS:= disjoint_include2_fold_left_lsubseq init_rs init_blks abs_ofs
                                                     res Heqres).
  assert (HFORALLB: List.forallb (MemBlock.inbounds_abs a)
                                 (snd (List.split init_blks)) = true).
  {
    assert (init_blks = inbounds_blocks m a).
    { unfold inbounds_blocks. rewrite <- Heqinit. reflexivity. }
    eapply inbounds_blocks_forallb.
    rewrite H. reflexivity.
  }
  eapply lsubseq_forallb.
  eassumption.
  assert (HLEN1: List.length (fst (init_rs, init_blks)) =
          List.length (snd (init_rs, init_blks))).
  { rewrite Heqinit. apply disjoint_include2_len.
    rewrite alive_P0_ranges_blocks_len. reflexivity.
  }
  simpl in HLEN1.
  assert (HLEN2: List.length (fst res) = List.length (snd res)).
  { rewrite Heqres.
    eapply disjoint_include2_fold_left_len.
    eassumption. reflexivity. }
  assert (HFINAL := lsubseq_combine init_rs (fst res) init_blks (snd res)
                                    HLEN1 HLEN2 HLSS).
  destruct HFINAL.
  rewrite HALL in *.
  eapply lsubseq_split_snd. assumption.
Qed.

Lemma inbounds_blocks2_filter:
  forall x l m,
    Ir.Memory.inbounds_blocks2 m (x :: l) =
      List.filter (fun b => Ir.MemBlock.inbounds_abs x b.(snd))
                  (Ir.Memory.inbounds_blocks2 m l).
Proof.
  intros.
  unfold Ir.Memory.inbounds_blocks2.
  simpl.
  rewrite disjoint_include2_fold_left_reorder.
  remember ((List.fold_left
             (fun (x0 : list (nat * nat) * list (Ir.blockid * Ir.MemBlock.t)) (ofs : nat)
              => disjoint_include2 (fst x0) (snd x0) ofs) l
             (Ir.Memory.alive_P0_ranges m, Ir.Memory.alive_blocks m))) as qq.
  dup Heqqq.
  eapply disjoint_include2_fold_left_rel in Heqqq0.
  2: eapply Ir.Memory.alive_blocks_P0_ranges.
  unfold disjoint_include2.
  unfold Ir.MemBlock.inbounds_abs.
  remember (List.split
       (List.filter
          (fun x0 : nat * nat * (Ir.blockid * Ir.MemBlock.t) => in_range x (fst x0))
          (List.combine (fst qq) (snd qq)))) as pp.
  dup Heqpp.
  eapply split_filter_combine_map in Heqpp.
  2: eassumption.
  destruct qq. simpl in *.
  destruct pp. simpl in *.
  eapply split_filter_combine_map2_snd in Heqpp0.
  2: rewrite Heqqq0.
  2: reflexivity.
  simpl in Heqpp0.
  assumption.
Qed.

Lemma inbounds_blocks2_lsubseq:
  forall (m:t) a abs_ofs blks1 blks2
         (HALL1:inbounds_blocks2 m (a::abs_ofs) = blks1)
         (HALL2:inbounds_blocks2 m abs_ofs = blks2),
    lsubseq blks2 blks1.
Proof.
  intros.
  unfold inbounds_blocks2 in *.
  simpl in HALL1.
  remember (alive_P0_ranges m) as P0s.
  remember (alive_blocks m) as blks.
  remember (disjoint_include2 P0s blks a) as init_res.
  assert (HLEN: List.length P0s = List.length blks).
  { rewrite HeqP0s. rewrite Heqblks.
    apply alive_P0_ranges_blocks_len. }
  assert (HLEN': List.length (fst init_res) = List.length (snd init_res)).
  { rewrite Heqinit_res. apply disjoint_include2_len. assumption. }
  remember (fold_left
               (fun (blks_and_ranges : list (nat * nat) * list (blockid * MemBlock.t))
                  (abs_ofs : nat) =>
                disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs)
               abs_ofs (disjoint_include2 P0s blks a)) as res2.
  remember (fold_left
               (fun (blks_and_ranges : list (nat * nat) * list (blockid * MemBlock.t))
                  (abs_ofs : nat) =>
                disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs)
               abs_ofs (P0s, blks)) as res1.
  assert (lsubseq (combine (fst res1) (snd res1)) (combine (fst res2) (snd res2))).
  { apply disjoint_include2_fold_left_lsubseq2 with
          (rs1 := P0s) (data1 := blks)
          (rs2 := init_res.(fst)) (data2 := init_res.(snd))
          (ofss := abs_ofs).
    - assumption.
    - rewrite Heqinit_res. apply disjoint_include2_len. assumption.
    - assumption.
    - rewrite <- Heqinit_res in Heqres2.
      destruct init_res.
      simpl. assumption.
    - apply disjoint_include2_lsubseq with (ofs := a).
      rewrite <- Heqinit_res. destruct init_res. reflexivity.
  }
  assert (HLEN1:List.length (fst res1) = List.length (snd res1)).
  { eapply disjoint_include2_fold_left_len.
    apply HLEN. eassumption. }
  assert (HLEN2:List.length (fst res2) = List.length (snd res2)).
  { eapply disjoint_include2_fold_left_len.
    apply HLEN'. rewrite <- Heqinit_res in *. destruct init_res.
    simpl. eassumption. }
  assert (lsubseq (fst res1) (fst res2) /\ lsubseq (snd res1) (snd res2)).
  { apply lsubseq_combine. assumption. assumption.
    assumption. }
  destruct H0.
  rewrite <- Heqinit_res in Heqres2.
  rewrite <- Heqres2 in HALL1.
  rewrite HALL2, HALL1 in H1.
  assumption.
Qed.

Lemma inbounds_blocks2_lsubseq2:
  forall (m : Ir.Memory.t) (abs_ofs1 abs_ofs2 : list nat)
    (blks1 blks2 : list (Ir.blockid * Ir.MemBlock.t))
    (HINB1:Ir.Memory.inbounds_blocks2 m abs_ofs1 = blks1)
    (HINB2:Ir.Memory.inbounds_blocks2 m abs_ofs2 = blks2)
    (HLSS:lsubseq abs_ofs1 abs_ofs2),
  lsubseq blks2 blks1.
Proof.
  intros.
  generalize dependent blks1.
  generalize dependent blks2.
  induction HLSS.
  { intros. unfold Ir.Memory.inbounds_blocks2 in HINB2.
    simpl in HINB2.
    unfold Ir.Memory.inbounds_blocks2 in HINB1.
    remember (List.fold_left
               (fun blks_and_ranges abs_ofs =>
                disjoint_include2 (fst blks_and_ranges)
                                  (snd blks_and_ranges) abs_ofs) l
               (Ir.Memory.alive_P0_ranges m, Ir.Memory.alive_blocks m)) as tmp.
    dup Heqtmp.
    eapply disjoint_include2_fold_left_lsubseq in Heqtmp.
    apply lsubseq_combine in Heqtmp.
    destruct Heqtmp. congruence.
    apply Ir.Memory.alive_P0_ranges_blocks_len.
    apply disjoint_include2_fold_left_len in Heqtmp0.
    congruence.
    apply Ir.Memory.alive_P0_ranges_blocks_len.
  }
  { intros.
    remember (Ir.Memory.inbounds_blocks2 m l1) as blks1'.
    symmetry in Heqblks1'.
    remember (Ir.Memory.inbounds_blocks2 m l2) as blks2'.
    symmetry in Heqblks2'.
    exploit IHHLSS. reflexivity. reflexivity.
    intros HH.
    rewrite inbounds_blocks2_filter in HINB1.
    rewrite inbounds_blocks2_filter in HINB2.
    rewrite Heqblks1' in HINB1.
    rewrite Heqblks2' in HINB2.
    eapply lsubseq_filter2.
    eapply HH.
    rewrite HINB2. reflexivity.
    rewrite HINB1. reflexivity.
  }
  { intros.
    remember (Ir.Memory.inbounds_blocks2 m l1) as blks1'.
    symmetry in Heqblks1'.
    exploit IHHLSS. reflexivity. reflexivity.
    intros HH.
    rewrite inbounds_blocks2_filter in HINB1.
    rewrite Heqblks1' in HINB1.
    eapply lsubseq_filter3.
    rewrite HINB2 in HH.
    eapply HH.
    rewrite HINB1. reflexivity.
  }
Qed.

(* Theorem: The results of inbounds_blocks2,
   contain all input offsets. *)
Lemma inbounds_blocks2_forallb2:
  forall (m:t) abs_ofs blks
         (HALL:inbounds_blocks2 m abs_ofs = blks),
    List.forallb (fun abs_ofs =>
                    List.forallb (MemBlock.inbounds_abs abs_ofs)
                                 (snd (List.split blks))) abs_ofs = true.
Proof.
  intros.
  generalize dependent blks.
  induction abs_ofs.
  - reflexivity.
  - simpl. intros.
    rewrite inbounds_blocks2_forallb with (m := m) (abs_ofs := abs_ofs).
    simpl.
    remember (inbounds_blocks2 m abs_ofs) as blks'.
    assert (lsubseq blks' blks).
    { apply inbounds_blocks2_lsubseq with (m := m) (a := a) (abs_ofs := abs_ofs).
      assumption. congruence. }
    apply forallb_implies with
      (fun o:nat => List.forallb (MemBlock.inbounds_abs o) (snd (List.split blks'))).
    + intros.
      eapply lsubseq_forallb. eassumption.
      apply lsubseq_split_snd. assumption.
    + apply IHabs_ofs.
      reflexivity.
    + assumption.
Qed.

(* Lemma: all blocks returned by inbounds_blocks2 are alive. *)
Lemma inbounds_blocks2_alive:
  forall (m:t) abs_ofs blks
         (HALL:inbounds_blocks2 m abs_ofs = blks),
    List.forallb (fun blk => MemBlock.alive blk.(snd)) blks = true.
Proof.
  intros.
  unfold inbounds_blocks2 in HALL.
  remember (alive_P0_ranges m) as rs.
  remember (alive_blocks m) as data.
  assert (List.length rs = List.length data).
  { rewrite Heqrs, Heqdata. apply alive_P0_ranges_blocks_len. }
  remember (fold_left
              (fun blks_and_ranges abs_ofs =>
               disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs)
              abs_ofs (rs, data)) as fl.
  assert (lsubseq (combine rs data) (combine (fst fl) (snd fl))).
  { eapply disjoint_include2_fold_left_lsubseq.
    apply Heqfl. }
  apply lsubseq_combine in H0.
  destruct H0.
  rewrite HALL in H1.
  apply lsubseq_forallb with (l := data).
  unfold alive_blocks in Heqdata.
  rewrite Heqdata.
  apply filter_forallb. assumption.
  assumption.
  erewrite disjoint_include2_fold_left_len.
  reflexivity. eassumption. eassumption.
Qed.

(* Lemma: there's no empty range in 'alive_P_ranges m'. *)
Lemma no_empty_range_alive_P_ranges:
  forall (m:t) (HWF:wf m),
    no_empty_range (alive_P_ranges m) = true.
Proof.
  intros.
  unfold alive_P_ranges.
  apply no_empty_range_concat.
  intros.
  apply In_map in HIN.
  destruct HIN.
  destruct H.
  rewrite <- H.
  apply (MemBlock.wf_poslen).
  destruct x.
  simpl in *.
  eapply wf_blocks.
  eassumption.
  eapply lsubseq_In.
  apply H0.
  apply blocks_alive_blocks_lsubseq.
Qed.

(* Lemma: inbounds_blocks2 with two different
   elements returns only one block. *)
Lemma inbounds_blocks2_singleton:
  forall (m:t) (ofs1 ofs2:nat) l (HWF:wf m)
         (HNEQ:~ (ofs1 = ofs2))
         (HINB:inbounds_blocks2 m (ofs1::ofs2::nil) = l),
    List.length l < 2.
Proof.
  intros.
  unfold inbounds_blocks2 in HINB.
  remember (alive_blocks m) as mbs.
  remember (alive_P0_ranges m) as P0s.
  assert (HLEN:List.length (alive_blocks m) = List.length (alive_P0_ranges m)).
  {
    unfold alive_P0_ranges.
    rewrite map_length.
    reflexivity.
  }
  simpl in HINB.
  remember (disjoint_include2 P0s mbs ofs1) as res1.
  assert (HLEN_RES1: List.length res1.(fst) = List.length res1.(snd)).
  {
    rewrite Heqres1.
    eapply disjoint_include2_len.
    congruence.
  }
  assert (List.length res1.(snd) < 3).
  {
    eapply inbounds_blocks_atmost_2.
    eassumption.
    rewrite inbounds_blocks_inbounds_blocks2.
    unfold inbounds_blocks2.
    simpl.
    rewrite <- HeqP0s.
    rewrite <- Heqmbs.
    rewrite Heqres1.
    reflexivity.
  }
  (* Okay, we showed that inbounds_blocks2 m (ofs1::nil) has
     less than 3 blocks. *)
  destruct res1 as [P0s1 mbs1].
  simpl in *.
  destruct (length mbs1) eqn:HLEN_MBS1.
  { (* length is 0. *)
    rewrite length_zero_iff_nil in HLEN_MBS1.
    rewrite length_zero_iff_nil in HLEN_RES1.
    rewrite HLEN_MBS1 in *.
    rewrite HLEN_RES1 in *.
    simpl in HINB. rewrite <- HINB. simpl. auto.
  }
  destruct n.
  { (* length is 1. *)
    apply list_len1 in HLEN_MBS1.
    apply list_len1 in HLEN_RES1.
    destruct HLEN_MBS1 as [h1 HLEN_MBS1].
    destruct HLEN_RES1 as [h2 HLEN_RES1].
    rewrite HLEN_MBS1, HLEN_RES1 in HINB.
    rewrite <- HINB.
    apply Lt.le_lt_n_Sm.
    apply disjoint_include2_len2.
  }
  destruct n.
  { (* length is 2. *)
    (* show that inbounds_blocks2 m (ofs2::ofs1::nil) has less than
       2 elements. *)
    remember (disjoint_include2 P0s1 mbs1 ofs2) as res2.
    remember (length l) as n' eqn:HLEN_MBS2.
    destruct n'.
    { auto. }
    destruct n'.
    { auto. }
    destruct n'.
    { (* Okay, let's show that this is impossible. *)
      apply list_len2 in HLEN_MBS1.
      apply list_len2 in HLEN_RES1.
      destruct HLEN_MBS1 as [mb1 HLEN_MBS1].
      destruct HLEN_MBS1 as [mb2 HLEN_MBS1].
      destruct HLEN_RES1 as [P01 HLEN_RES1].
      destruct HLEN_RES1 as [P02 HLEN_RES1].
      symmetry in HLEN_MBS2.
      destruct res2 as [P0s2 mbs2].
      assert (length P0s1 = length mbs1).
      { rewrite HLEN_MBS1.
        rewrite HLEN_RES1.
        reflexivity.
      }
      assert (lsubseq P0s1 P0s2 /\ lsubseq mbs1 mbs2).
      {
        apply lsubseq_combine.
        - assumption.
        - replace (length P0s2) with (length (fst (P0s2, mbs2))).
          replace (length mbs2) with (length (snd (P0s2, mbs2))).
          rewrite Heqres2.
          apply disjoint_include2_len.
          assumption.
          reflexivity. reflexivity.
        - apply disjoint_include2_lsubseq with (ofs := ofs2).
          rewrite <- Heqres2.
          reflexivity.
      }
      assert (length P0s2 = length mbs2).
      {
        assert (P0s2 = fst (disjoint_include2 P0s1 mbs1 ofs2)).
        { rewrite <- Heqres2. reflexivity. }
        assert (mbs2 = snd (disjoint_include2 P0s1 mbs1 ofs2)).
        { rewrite <- Heqres2. reflexivity. }
        rewrite H2.
        rewrite H3.
        apply disjoint_include2_len.
        assumption.
      }
      assert (mbs2 = mbs1).
      {
        symmetry.
        apply lsubseq_full.
        - destruct H1. assumption.
        - rewrite <- HINB in HLEN_MBS2.
          simpl in HLEN_MBS2.
          rewrite HLEN_MBS1. rewrite HLEN_MBS2.
          reflexivity.
      }
      assert (P0s2 = P0s1).
      {
        symmetry.
        apply lsubseq_full.
        - destruct H1. assumption.
        - rewrite H0. rewrite H2. rewrite H3. reflexivity.
      }
      rewrite H3 in *. clear H3.
      rewrite H4 in *. clear H4.
      simpl in HINB.
      rewrite <- HINB in *. clear HINB.
      clear H2.
      assert (HP0 := alive_blocks_P0_ranges m).
      assert (map (fun mb : blockid * MemBlock.t => MemBlock.P0_range (snd mb))
                  (P0s1, mbs1).(snd) = (P0s1, mbs1).(fst)).
      {
        eapply split_filter_combine_map.
        apply HP0.
        unfold disjoint_include2 in Heqres1.
        rewrite <- HeqP0s. rewrite <- Heqmbs.
        apply Heqres1.
      }
      (* Okay, now show that two ranges:
         MemBlock.P0_range (snd mb1),
         MemBlock.P0_range (snd mb2) are disjoint, and
         they include ofs1. *)
      assert (lsubseq P0s P0s1 /\ lsubseq mbs mbs1).
      {
        apply lsubseq_combine.
        - rewrite HeqP0s.
          rewrite Heqmbs.
          apply alive_P0_ranges_blocks_len.
        - assumption.
        - apply disjoint_include2_lsubseq with (ofs := ofs1).
          rewrite Heqres1. reflexivity.
      }
      assert (HNOEMPTY: no_empty_range (P01::P02::nil) = true).
      {
        apply no_empty_range_lsubseq with (l1 := alive_P0_ranges m).
        - apply no_empty_range_lsubseq with (l1 := alive_P_ranges m). 
          + apply no_empty_range_alive_P_ranges.
            assumption.
          + apply alive_P_P0_ranges_lsubseq.
            assumption.
        - rewrite <- HLEN_RES1.
          assert (P0s1 = fst (disjoint_include2 P0s mbs ofs1)).
          { rewrite <- Heqres1. reflexivity. }
          rewrite H4.
          rewrite disjoint_include_include2.
          rewrite HeqP0s.
          apply disjoint_include_lsubseq.
          rewrite HeqP0s.
          rewrite Heqmbs.
          congruence.
      }
      simpl in HNOEMPTY.
      rewrite andb_true_r in HNOEMPTY.
      rewrite andb_true_iff in HNOEMPTY.
      repeat (rewrite Nat.ltb_lt in HNOEMPTY).
      assert (disjoint_ranges (P01::P02::nil) = true).
      {
        apply disjoint_lsubseq_disjoint with (rs := P0s).
        - rewrite HeqP0s.
          apply disjoint_lsubseq_disjoint with (rs := alive_P_ranges m).
          + apply wf_disjoint. assumption.
          + apply alive_P_P0_ranges_lsubseq. assumption.
        - destruct H3.
          rewrite HLEN_RES1 in H3.
          assumption.
      }
      assert (in_range ofs1 P01 = true /\ in_range ofs1 P02 = true).
      {
        apply inrange2_forallb.
        apply disjoint_include_inrange with (rs := P0s).
        erewrite <- disjoint_include_include2.
        rewrite <- Heqres1.
        rewrite HLEN_RES1.
        reflexivity.
        congruence.
      }
      assert (in_range ofs2 P01 = true /\ in_range ofs2 P02 = true).
      {
        apply inrange2_forallb.
        apply disjoint_include_inrange with (rs := P0s1).
        erewrite <- disjoint_include_include2.
        rewrite <- Heqres2.
        rewrite HLEN_RES1.
        reflexivity.
        congruence.
      }
      (* Then, we can use inrange2_disjoint to show
         (b1 + l1 = b2 /\ i = b2) \/ (b2 + l2 = b1 /\ i = b1).
         And then we show that for i' != i,
         in_range i' (b1, l1) && in_range i' (b2, l2) = false,
         using inrange2_false.
      *)
      destruct P01 as [mb1beg mb1len].
      destruct P02 as [mb2beg mb2len].
      simpl in HNOEMPTY.
      destruct HNOEMPTY as [HNOEMPTY1 HNOEMPTY2].
      destruct H5 as [HINR11 HINR12].
      destruct H6 as [HINR21 HINR22].
      assert (HCOND1 := inrange2_disjoint mb1beg mb1len mb2beg mb2len ofs1
                                          HINR11 HINR12 H4).
      assert (HCOND2 := inrange2_disjoint mb1beg mb1len mb2beg mb2len ofs2
                                          HINR21 HINR22 H4).
      exfalso.
      destruct HCOND1 as [HCOND1 | HCOND1];
        destruct HCOND2 as [HCOND2 | HCOND2].
      - apply HNEQ.
        destruct HCOND1. destruct HCOND2. congruence.
      - destruct HCOND1 as [HCOND1 _].
        destruct HCOND2 as [HCOND2 _].
        rewrite <- HCOND2 in HCOND1.
        rewrite <- Nat.add_assoc in HCOND1.
        assert (HLEN': 0 < mb2len + mb1len).
        { apply Nat.add_pos_r.
          assumption. }
        assert (HFALSE := Nat.lt_add_pos_r (mb2len + mb1len) mb2beg HLEN').
        rewrite HCOND1 in HFALSE.
        eapply Nat.lt_irrefl.
        eassumption.
      - destruct HCOND1 as [HCOND1 _].
        destruct HCOND2 as [HCOND2 _].
        rewrite <- HCOND2 in HCOND1.
        rewrite <- Nat.add_assoc in HCOND1.
        assert (HLEN': 0 < mb1len + mb2len).
        { apply Nat.add_pos_r.
          assumption. }
        assert (HFALSE := Nat.lt_add_pos_r (mb1len + mb2len) mb1beg HLEN').
        rewrite HCOND1 in HFALSE.
        eapply Nat.lt_irrefl.
        eassumption.
      - destruct HCOND1. destruct HCOND2. congruence.
    }
    { (* The result cannot have more than 2 elements *)
      rewrite <- HINB in HLEN_MBS2.
      rewrite Heqres2 in HLEN_MBS2.
      rewrite <- disjoint_include2_len in HLEN_MBS2.
      rewrite disjoint_include_include2 in HLEN_MBS2.
      remember (disjoint_include P0s1 ofs2) as r.
      assert (lsubseq P0s1 r).
      { rewrite Heqr. apply disjoint_include_lsubseq. }
      assert (~lsubseq P0s1 r).
      { apply lsubseq_exceed.
        rewrite <- HLEN_MBS2.
        rewrite HLEN_RES1.
        omega.
      }
      exfalso. apply H1. assumption.
      congruence.
      congruence.
    }
  }
  {
    exfalso.
    eapply Lt.le_not_lt.
    apply Nat.le_add_r.
    assert (S (S (S n)) =  3+n). (* Why should I do this? :( *)
    reflexivity.
    rewrite H0 in H.
    apply H.
  }
Qed.

(* Lemma: inbounds_blocks2 with at least two different
   elements returns only one block. *)
Lemma inbounds_blocks2_singleton2:
  forall (m:t) (ofs1 ofs2:nat) l ofs' (HWF:wf m)
         (HNEQ:~ (ofs1 = ofs2))
         (HINB:inbounds_blocks2 m (ofs1::ofs2::ofs') = l),
    List.length l < 2.
Proof.
  intros.
  unfold inbounds_blocks2 in HINB.
  simpl in HINB.
  remember (alive_P0_ranges m) as P0.
  remember (alive_blocks m) as blks.
  
  remember (disjoint_include2 P0 blks ofs1) as res1.
  assert (lsubseq (List.combine P0 blks) (List.combine res1.(fst) res1.(snd))).
  { apply disjoint_include2_lsubseq with (ofs := ofs1).
    rewrite <- Heqres1. destruct res1. reflexivity. }
  assert (List.length res1.(fst) = List.length res1.(snd)).
  { rewrite Heqres1.
    apply disjoint_include2_len.
    rewrite HeqP0. rewrite Heqblks. rewrite alive_P0_ranges_blocks_len.
    reflexivity.
  }

  remember (disjoint_include2 (fst res1) (snd res1) ofs2) as res2.
  assert (lsubseq (List.combine res1.(fst) res1.(snd))
                  (List.combine res2.(fst) res2.(snd))).
  { apply disjoint_include2_lsubseq with (ofs := ofs2).
    rewrite <- Heqres2. destruct res2; reflexivity. }
  assert (List.length res2.(fst) = List.length res2.(snd)).
  { rewrite Heqres2.
    apply disjoint_include2_len. congruence.
  }

  remember (fold_left
              (fun (blks_and_ranges : list (nat * nat) * list (blockid * MemBlock.t))
                 (abs_ofs : nat) =>
               disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs)
              ofs' res2) as res3.
  assert (lsubseq (List.combine res2.(fst) res2.(snd))
                  (List.combine res3.(fst) res3.(snd))).
  {
    apply disjoint_include2_fold_left_lsubseq with (ofss := ofs').
    destruct res2.
    simpl.
    assumption.
  }
  assert (List.length res3.(fst) = List.length res3.(snd)).
  { eapply disjoint_include2_fold_left_len.
    eapply H2.
    destruct res2. simpl. eapply Heqres3.
  }

  assert (res2.(snd) = inbounds_blocks2 m (ofs1::ofs2::nil)).
  {
    unfold inbounds_blocks2.
    simpl.
    rewrite <- HeqP0.
    rewrite <- Heqblks.
    rewrite <- Heqres1.
    rewrite <- Heqres2.
    reflexivity.
  }
  assert (length (snd res2) < 2).
  {
    apply inbounds_blocks2_singleton with (m := m) (ofs1 := ofs1) (ofs2 := ofs2).
    assumption.
    assumption.
    congruence.
  }
  assert (HLS:lsubseq (fst res2) (fst res3) /\ lsubseq (snd res2) (snd res3)).
  { apply lsubseq_combine.
    assumption.
    assumption.
    assumption.
  }
  destruct HLS.
  rewrite <- HINB.
  assert (length (snd res3) <= length (snd res2)).
  { apply lsubseq_len. assumption. }
  eapply Nat.le_lt_trans.
  - eassumption.
  - assumption.
Qed.

(* Lemma: if there's alive block blk, which has abs_ofs1 & abs_ofs2
   as its inbounds, blk must be included in the result of inbounds_blocks2. *)
Lemma inbounds_blocks2_In:
  forall (m:t) (bid:blockid) (blk:MemBlock.t) blks abs_ofs1 abs_ofs2
         (HBLK: Some blk = get m bid)
         (HRES: blks = inbounds_blocks2 m (abs_ofs1::abs_ofs2::nil))
         (HALIVE: MemBlock.alive blk = true)
         (HINB1: MemBlock.inbounds_abs abs_ofs1 blk = true)
         (HINB2: MemBlock.inbounds_abs abs_ofs2 blk = true)
         (HNEQ: abs_ofs1 <> abs_ofs2),
    List.In (bid, blk) blks.
Proof.
  intros.
  unfold inbounds_blocks2 in HRES.
  unfold MemBlock.inbounds_abs in HINB1, HINB2.
  simpl in HRES.
  remember (disjoint_include2 (alive_P0_ranges m) (alive_blocks m) abs_ofs1) as res1.
  assert (List.In (MemBlock.P0_range blk, (bid, blk))
                  (List.combine (fst res1) (snd res1))).
  {
    apply disjoint_include2_In with (rs := alive_P0_ranges m)
        (data := alive_blocks m) (i := abs_ofs1).
    rewrite alive_P0_ranges_blocks_len. reflexivity.
    apply combine_map_In with (f := fun x => MemBlock.P0_range x.(snd)).
    - reflexivity.
    - apply alive_blocks_P0_ranges.
    - apply alive_blocks_In with (m := m).
      assumption. assumption. reflexivity.
    - assumption.
    - assumption.
  }
  remember (disjoint_include2 (fst res1) (snd res1) abs_ofs2) as res2.
  assert (List.In (MemBlock.P0_range blk, (bid, blk))
                  (List.combine (fst res2) (snd res2))).
  {
    apply disjoint_include2_In with (rs := fst res1) (data := snd res1)
                                    (i := abs_ofs2).
    - rewrite Heqres1. rewrite disjoint_include2_len. reflexivity.
      apply alive_P0_ranges_blocks_len.
    - assumption.
    - assumption.
    - assumption.
  }
  rewrite HRES.
  eapply in_combine_r.
  eassumption.
Qed.

Lemma inbounds_blocks2_In2:
  forall m b t Is
         (HBT: b::t = Ir.Memory.inbounds_blocks2 m Is),
    List.In b (Ir.Memory.blocks m).
Proof.
  intros.
  unfold inbounds_blocks2 in HBT.
  remember (alive_P0_ranges m) as x.
  remember (alive_blocks m) as y.
  remember (fold_left
             (fun (blks_and_ranges : list (nat * nat) * list (blockid * MemBlock.t))
                (abs_ofs : nat) =>
              disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs) Is
             (x, y)) as res.
  assert (lsubseq (combine x y) (combine (fst res) (snd res))).
  { eapply disjoint_include2_fold_left_lsubseq.
    eassumption. }
  apply lsubseq_combine in H.
  destruct H.
  rewrite <- HBT in H0.
  assert (lsubseq (blocks m) (b::t0)).
  { eapply lsubseq_trans.
    apply blocks_alive_blocks_lsubseq.
    rewrite Heqy in H0. assumption. }
  apply lsubseq_In with (l' := b::t0).
  + simpl. left. reflexivity.
  + assumption.
  + rewrite Heqx, Heqy.
    apply alive_P0_ranges_blocks_len.
  + apply disjoint_include2_fold_left_len with (rs := x) (data := y) (ofss := Is).
    rewrite Heqx, Heqy.
    apply alive_P0_ranges_blocks_len.
    assumption.
Qed.

Lemma inbounds_blocks2_intersect:
  forall m l i1 i2 I I' l'
         (HWF:Ir.Memory.wf m)
         (HDIFF:i1 <> i2)
         (HINB1:Ir.Memory.inbounds_blocks2 m (i1::i2::I) = l)
         (HINB2:Ir.Memory.inbounds_blocks2 m (i1::i2::I') = l'),
    l = l' \/ l = [] \/ l' = [].
Proof.
  intros.
  dup HINB1.
  apply Ir.Memory.inbounds_blocks2_singleton2 in HINB0.
  dup HINB2.
  apply Ir.Memory.inbounds_blocks2_singleton2 in HINB3.
  destruct l.
  { eauto. }
  destruct l.
  { destruct l'. eauto.
    destruct l'.
    { destruct p. destruct p0.
      destruct (b =? b0) eqn:HEQID.
      { rewrite PeanoNat.Nat.eqb_eq in HEQID.
        subst b0.
        assert (List.In (b, t0) (Ir.Memory.blocks m)).
        { eapply Ir.Memory.inbounds_blocks2_In2.
          rewrite HINB1. reflexivity. }
        assert (List.In (b, t1) (Ir.Memory.blocks m)).
        { eapply Ir.Memory.inbounds_blocks2_In2.
          rewrite HINB2. reflexivity. }
        eapply Ir.Memory.blocks_get in H; try eassumption; try reflexivity.
        eapply Ir.Memory.blocks_get in H0; try eassumption; try reflexivity.
        simpl in *. left. congruence. }
      { rewrite PeanoNat.Nat.eqb_neq in HEQID.
        dup HINB1.
        dup HINB2.
        eapply Ir.Memory.inbounds_blocks2_forallb2 in HINB4.
        simpl in HINB4.
        repeat (rewrite andb_true_r in HINB4).
        eapply Ir.Memory.inbounds_blocks2_forallb2 in HINB5.
        simpl in HINB5.
        repeat (rewrite andb_true_r in HINB5).
        (* make alive *)
        dup HINB1.
        apply Ir.Memory.inbounds_blocks2_alive in HINB6. simpl in HINB6.
        rewrite andb_true_r in HINB6.
        dup HINB2.
        apply Ir.Memory.inbounds_blocks2_alive in HINB7. simpl in HINB7.
        rewrite andb_true_r in HINB7.
        (* inbounds_blocks2 -> List.In *)
        symmetry in HINB1.
        eapply Ir.Memory.inbounds_blocks2_In2 in HINB1.
        symmetry in HINB2.
        eapply Ir.Memory.inbounds_blocks2_In2 in HINB2.
        rewrite andb_true_iff in HINB4. destruct HINB4.
        rewrite andb_true_iff in H0. destruct H0.
        rewrite andb_true_iff in HINB5. destruct HINB5.
        rewrite andb_true_iff in H3. destruct H3.
        dup HWF. inv HWF.
        assert (disjoint_ranges (Ir.Memory.alive_P0_ranges m) = true).
        { eapply disjoint_lsubseq_disjoint.
          eapply wf_disjoint0.
          eapply Ir.Memory.alive_P_P0_ranges_lsubseq.
          assumption. }
        assert (disjoint_range (Ir.MemBlock.P0_range t0)
                               (Ir.MemBlock.P0_range t1) = true).
        { eapply Ir.Memory.disjoint_range_P0_range.
          eassumption.
          apply In_get in HINB1; try assumption. eassumption.
          assumption.
          apply In_get in HINB2; try assumption. eassumption.
          assumption.
          assumption. }
        (* okay, now let's get inconsistency. *)
        unfold Ir.MemBlock.P0_range in H6.
        simpl in H6.
        unfold disjoint_range in H6.
        rewrite orb_true_iff in H6.
        rewrite PeanoNat.Nat.leb_le in H6.
        rewrite PeanoNat.Nat.leb_le in H6.
        unfold Ir.MemBlock.inbounds_abs in H, H0, H2, H3.
        unfold in_range in H, H0, H2, H3.
        rewrite andb_true_iff in H, H0, H2, H3.
        unfold Ir.MemBlock.P0_range in H, H0, H2, H3.
        simpl in H, H0, H2, H3.
        repeat (rewrite PeanoNat.Nat.leb_le in *).
        omega.
      }
    }
    simpl in HINB3.
    omega.
  }
  simpl in HINB0. omega.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma inbounds_blocks2_In3:
  forall m bid mb bwid o
         (HGET:Some mb = Memory.get m bid)
         (HSZ :bwid > 0)
         (HINB:MemBlock.inbounds_abs o mb &&
               MemBlock.inbounds_abs (o + bwid) mb = true)
         (HALIVE:MemBlock.alive mb = true),
    List.In (bid, mb) (inbounds_blocks2 m (o::(o + bwid)::nil)).
Proof.
  intros.
  rewrite andb_true_iff in HINB.
  destruct HINB.
  eapply inbounds_blocks2_In.
  eassumption.
  reflexivity.
  assumption.
  assumption.
  assumption.
  omega.
Qed.

Lemma inbounds_blocks2_same:
  forall m1 m2 bid mb bwid o
         (HGET:Some mb = get m1 bid)
         (HWF2:wf m2)
         (HSAME:get m1 bid = get m2 bid)
         (HSZ:bwid > 0)
         (HINB:inbounds_blocks2 m1 (o::(o + bwid)::nil) = (bid, mb)::nil),
    inbounds_blocks2 m1 (o::(o + bwid)::nil) =
    inbounds_blocks2 m2 (o::(o + bwid)::nil).
Proof.
  intros.
  rewrite HINB.
  dup HINB.
  apply inbounds_blocks2_forallb2 in HINB.
  apply inbounds_blocks2_alive in HINB0.
  simpl in HINB.
  simpl in HINB0.
  repeat (rewrite andb_true_r in HINB).
  repeat (rewrite andb_true_r in HINB0).

  remember (inbounds_blocks2 m2 (o::(o + bwid)::nil)) as ib.
  assert (List.In (bid, mb) ib).
  { rewrite Heqib. apply inbounds_blocks2_In3; try assumption. congruence. }
  symmetry in Heqib.
  apply inbounds_blocks2_singleton in Heqib; try omega.
  destruct ib. inv H.
  destruct ib. inv H. reflexivity. inv H0. simpl in Heqib. omega.
  assumption.
Qed.

Lemma inbounds_blocks2_Permutation:
  forall m l I I'
         (HPERM:Permutation I I')
         (HINB:inbounds_blocks2 m I = l),
    inbounds_blocks2 m I' = l.
Proof.
  intros.
  unfold inbounds_blocks2 in *.
  simpl in HINB.
  remember (List.fold_left
              (fun blks_and_ranges abs_ofs =>
               disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs) I
              (alive_P0_ranges m, alive_blocks m)) as ll.
  symmetry in Heqll.
  apply disjoint_include2_fold_left_Permutation with (I'0 := I') in Heqll.
  rewrite Heqll. assumption. assumption.
Qed.

Lemma inbounds_blocks2_cons:
  forall m I i bid mb
         (HINB:inbounds_blocks2 m I = (bid, mb)::nil),
    (in_range i (MemBlock.P0_range mb) = true ->
     inbounds_blocks2 m (i::I) = (bid, mb)::nil) /\
    (in_range i (MemBlock.P0_range mb) = false ->
     inbounds_blocks2 m (i::I) = nil).
Proof.
  intros.
  dup HINB.
  unfold inbounds_blocks2 in *.
  simpl.
  remember ((List.fold_left
              (fun blks_and_ranges abs_ofs =>
               disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs) I
              (alive_P0_ranges m, alive_blocks m))) as tt.
  destruct tt.
  assert (List.map (fun mb => MemBlock.P0_range mb.(snd))
                   (alive_blocks m) = alive_P0_ranges m).
  { apply alive_blocks_P0_ranges. }
  assert (List.length (alive_P0_ranges m) =
          List.length (alive_blocks m)).
  { apply alive_P0_ranges_blocks_len. }
  assert (List.length l = List.length l0).
  { apply disjoint_include2_fold_left_len in Heqtt.
    simpl in Heqtt. congruence. assumption. }
  assert (lsubseq (List.combine (alive_P0_ranges m)
                                (alive_blocks m))
                  (List.combine l l0)).
  { replace l with (fst (l, l0)) by reflexivity.
    replace l0 with (snd (l, l0)) at 2 by reflexivity.
    replace (alive_P0_ranges m) with
        (fst ((alive_P0_ranges m), alive_blocks m)) by reflexivity.
    replace (alive_blocks m) with
        (snd ((alive_P0_ranges m), alive_blocks m))
      at 2 by reflexivity.
    eapply disjoint_include2_fold_left_lsubseq.
    { eassumption. }
  }
  assert (List.map (fun mb => MemBlock.P0_range mb.(snd)) l0 = l).
  { eapply lsubseq_combine_map in H2; eassumption. }
  simpl in HINB.
  rewrite HINB in H3.
  simpl in H3.

  split.
  { intros HH0.
    rewrite disjoint_include2_fold_left_reorder.
    rewrite <- Heqtt. simpl. simpl in HINB. rewrite HINB. rewrite <- H3.
    unfold disjoint_include2. simpl.
    rewrite HH0. simpl. reflexivity. }
  { intros HH0.
    rewrite disjoint_include2_fold_left_reorder.
    rewrite <- Heqtt. simpl. simpl in HINB. rewrite HINB. rewrite <- H3.
    unfold disjoint_include2. simpl.
    rewrite HH0. simpl. reflexivity. }
Qed.

Lemma inbounds_blocks2_cons2:
  forall m I i
         (HINB:inbounds_blocks2 m I = nil),
    inbounds_blocks2 m (i::I) = nil.
Proof.
  intros.
  dup HINB.
  unfold inbounds_blocks2 in *.
  simpl.
  rewrite disjoint_include2_fold_left_reorder.
  remember ((List.fold_left
               (fun
                  (blks_and_ranges : list (nat * nat) * list (Ir.blockid * MemBlock.t))
                  (abs_ofs : nat) =>
                disjoint_include2 (fst blks_and_ranges) (snd blks_and_ranges) abs_ofs) I
               (alive_P0_ranges m, alive_blocks m))) as fl.
  destruct fl.
  assert (length (fst (l, l0)) = length (snd (l, l0))).
  { 
    eapply disjoint_include2_fold_left_len.
    eapply alive_P0_ranges_blocks_len.
    eassumption. }
  simpl in H. simpl in HINB.
  destruct l. simpl. reflexivity.
  rewrite HINB in H. simpl in H. omega.
Qed.

Lemma inbounds_blocks2_singleton3:
  forall m bid mb ofs1 ofs2
    (HWF:Ir.Memory.wf m)
    (HGET:Some mb = Ir.Memory.get m bid)
    (HALIVE:Ir.MemBlock.alive mb = true)
    (HOFS:ofs1 <> ofs2)
    (HINB1:Ir.MemBlock.inbounds_abs ofs1 mb = true)
    (HINB2:Ir.MemBlock.inbounds_abs ofs2 mb = true),
    Ir.Memory.inbounds_blocks2 m [ofs1; ofs2] = [(bid, mb)].
Proof.
  intros.
  remember (Ir.Memory.inbounds_blocks2 m [ofs1; ofs2]) as blk.
  dup Heqblk.
  symmetry in Heqblk.
  eapply Ir.Memory.inbounds_blocks2_singleton in Heqblk; try assumption.
  eapply Ir.Memory.inbounds_blocks2_In in Heqblk0; try eassumption.
  destruct blk. inv Heqblk0.
  destruct blk. inv Heqblk0. reflexivity. inv H. simpl in Heqblk.
  omega.
Qed.

Lemma inbounds_blocks2_singleton4:
  forall (m:Ir.Memory.t) (ofs1 ofs2:nat) ofs' bid mb
         (HWF:Ir.Memory.wf m)
         (HGET:Some mb = Ir.Memory.get m bid)
         (HALIVE:Ir.MemBlock.alive mb = true)
         (HNEQ:ofs1 <> ofs2)
         (HFORALLB:List.forallb
                     (fun i => Ir.MemBlock.inbounds_abs i mb)
                     (ofs1::ofs2::ofs') = true),
    Ir.Memory.inbounds_blocks2 m (ofs1::ofs2::ofs') = [(bid, mb)].
Proof.
  intros.
  assert (Ir.Memory.inbounds_blocks2 m (ofs1::ofs2::nil) = [(bid, mb)]).
  { simpl in HFORALLB.
    rewrite andb_true_iff in HFORALLB.
    destruct HFORALLB.
    rewrite andb_true_iff in H0.
    destruct H0.
    eapply inbounds_blocks2_singleton3; try eassumption. }
  (* okay.. now we shuld do induction on ofs'.
     Prior to that, do permutation. *)
  assert (Ir.Memory.inbounds_blocks2 m (ofs1 :: ofs2 :: ofs') =
          Ir.Memory.inbounds_blocks2 m (ofs' ++ (ofs1::ofs2::nil))).
  { erewrite Ir.Memory.inbounds_blocks2_Permutation
    with (I := (ofs' ++ [ofs1; ofs2])).
    reflexivity.
    replace (ofs1::ofs2::ofs') with ((ofs1::ofs2::nil) ++ ofs') by reflexivity.
    eapply Permutation_app2. reflexivity.
  }
  rewrite H0.
  clear H0.
  clear HNEQ.
  simpl in HFORALLB.
  rewrite andb_true_iff in HFORALLB.
  destruct HFORALLB.
  rewrite andb_true_iff in H1.
  destruct H1.
  clear H0. clear H1.
  (* okay ready. *)
  induction ofs'.
  { simpl. assumption. }
  { simpl.
    simpl in H2.
    rewrite andb_true_iff in H2.
    destruct H2.
    apply IHofs' in H1.
    apply Ir.Memory.inbounds_blocks2_cons with (i := a) in H1.
    assert (in_range a (Ir.MemBlock.P0_range mb) = true).
    { unfold Ir.MemBlock.inbounds_abs in H0.
      assumption.
    }
    apply H1 in H2.
    assumption.
  }
Qed.

Lemma zeroofs_block_addr:
  forall mb bid m (HGET:Ir.Memory.get m bid = Some mb)
         (HWF:Ir.Memory.wf m)
         (HALIVE:Ir.MemBlock.alive mb = true),
    Ir.Memory.zeroofs_block m (Ir.MemBlock.addr mb) = Some (bid, mb).
Proof.
  intros.
  unfold Ir.Memory.zeroofs_block.
  remember (Ir.Memory.inbounds_blocks2 m
    [Ir.MemBlock.addr mb; Ir.MemBlock.addr mb + 1]) as blks.
  symmetry in Heqblks.
  dup Heqblks.
  assert (List.In (bid, mb) blks).
  { rewrite <- Heqblks0.
    eapply Ir.Memory.inbounds_blocks2_In3.
    congruence. omega.
    unfold Ir.MemBlock.inbounds_abs.
    rewrite andb_true_iff.
    unfold in_range.
    unfold Ir.MemBlock.P0_range.
    simpl.
    rewrite Nat.leb_refl.
    assert (1 <= Ir.MemBlock.n mb).
    { eapply Ir.MemBlock.n_pos. inv HWF.
      exploit wf_blocks0.
      symmetry in HGET.
      eapply Ir.Memory.get_In in HGET. eassumption. reflexivity.
      eauto. }
    simpl.
    repeat (rewrite andb_true_iff).
    repeat (rewrite PeanoNat.Nat.leb_le).
    omega.
    assumption.
  }
  eapply Ir.Memory.inbounds_blocks2_singleton in Heqblks.
  destruct blks. inv H.
  destruct blks.
  inv H. simpl. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
  inv H0. simpl in Heqblks. omega.
  assumption.
  omega.
Qed.



End Memory.

End Ir.
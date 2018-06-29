Require Import Common.
Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import PeanoNat.
Require Import Omega.

Module Ir.

Definition PTRSZ := 16.
Definition MEMSZ := Nat.shiftl 1 PTRSZ.
Definition TWINCNT := 3.

Definition blockid := nat.
Definition callid := nat.
Definition time := nat.

Inductive ptrval :=
(*
-- Log(l, o) where 0 <= o < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
*)
| plog: blockid * nat -> ptrval
(*
- Phy(o, I, cid) where 0 <= o, i(¡ô I) < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
*)
| pphy: nat * list nat * option callid -> ptrval.


(* NULL pointer. *)
Definition NULL := pphy (0, nil, None).


(* Are two pointers equivalent? *)
Definition ptr_eqb (p1 p2:ptrval): bool :=
  match (p1, p2) with
  | (plog (bid1, ofs1), plog (bid2, ofs2)) =>
    Nat.eqb bid1 bid2 && Nat.eqb ofs1 ofs2
  | (pphy (ofs1, I1, cid1), pphy (ofs2, I2, cid2)) =>
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
  - destruct p.
    repeat (rewrite Nat.eqb_refl). reflexivity.
  - destruct p. destruct p.
    rewrite Nat.eqb_refl.
    rewrite list_inclb_refl.
    destruct o. rewrite Nat.eqb_refl. reflexivity. reflexivity.
Qed.



Inductive blockty :=
| stack | heap | global | function.


Module Bit.

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

Theorem N_bits_N:
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

Theorem from_bits_to_bits:
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

(* Returns (start_ofs, size)s including all twin blocks. *)
Definition P_ranges (mb:t):list (nat * nat) :=
  List.map (fun ofs => (ofs, mb.(n))) mb.(P).

(* Returns integer address of the block. *)
Definition addr (mb:t): nat :=
  List.hd 0 mb.(P).

(* Returns (start_ofs, size) of the using one. *)
Definition P0_range (mb:t): nat * nat :=
  (addr mb, mb.(n)).


Structure wf (mb:t) := mkWf
  {
    wf_tcond: forall t (FREED:mb.(r).(snd) = Some t), mb.(r).(fst) < t;
    wf_clen: List.length mb.(c) = mb.(n);
    (* wf_poslen: There's no zero-size block in the memory.
       In this formalization, malloc(0) returns NULL, so this invariant
       holds. *)
    wf_poslen: no_empty_range (P_ranges mb) = true;
    wf_align: forall p (HAS:List.In p mb.(P)), Nat.modulo p mb.(a) = 0;
    wf_inmem: forall p (HAS:List.In p mb.(P)), p + mb.(n) <= MEMSZ;
    wf_notnull: forall p (HAS:List.In p mb.(P)), ~ (p = 0);
    wf_disj: disjoint_ranges (P_ranges mb) = true;
    wf_twin: List.length mb.(P) = TWINCNT
  }.

Definition alive (mb:t): bool :=
  match mb.(r).(snd) with
  | None => true | Some _ => false
  end.

Definition alive_before (the_time:nat) (mb:t): bool :=
  Nat.ltb mb.(r).(fst) the_time.

Definition inbounds (ofs:nat) (mb:t): bool :=
  Nat.leb ofs mb.(n).

Definition inbounds_abs (ofs':nat) (mb:t): bool :=
  in_range ofs' (P0_range mb).

(* offset, len *)
Definition bytes (mb:t) (ofs len:nat): list (Byte.t) :=
  List.firstn len (List.skipn ofs mb.(c)).

Definition set_bytes (mb:t) (ofs:nat) (bytes:list (Byte.t)): t :=
  mk mb.(bt) mb.(r) mb.(n) mb.(a)
     (List.firstn ofs (mb.(c)) ++ bytes ++
      List.skipn (ofs + List.length bytes) mb.(c))
     mb.(P).

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
  match (inbounds_blocks m abs_ofs) with
  | nil => None
  | t =>
    match (List.filter (fun mb => Nat.eqb (MemBlock.addr mb.(snd)) abs_ofs) t) with
    | nil => None
    | h::t' => Some h
    end
  end.

(* Well-formedness of memory. *)
Structure wf (m:t) :=
  {
    wf_blocks: forall i p (HAS:List.In (i, p) m.(blocks)), MemBlock.wf p;
    wf_uniqueid: List.NoDup (List.map fst m.(blocks));
    wf_disjoint: disjoint_ranges (alive_P_ranges m) = true;
  }.


(* Add a new memory block. *)
Definition new (m:t) (t:blockty) (n:nat) (a:nat) (c:list Byte.t) (P:list nat)
           (HALIGN: forall n (HIN:List.In n P), Nat.modulo n a = 0)
           (HDISJ: allocatable m (List.map (fun x => (x, n)) P) = true)
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
     (List.map (fun mbid => if Nat.eqb mbid.(fst) i then (i, mb) else mbid)
               m.(blocks))
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
        | Some mb' => Some (incr_time (set m i mb'))
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


(**********************************************
    Lemmas&Theorems about get/set functions
 **********************************************)      

Lemma map_key_In_id {X:Type}:
  forall (l:list (nat * X)) (key:nat) (val:X)
         (HIN:List.In (key, val) l)
         (HNODUP:List.NoDup (List.map fst l)),
  List.map (fun x => if fst x =? key then (key, val) else x)
       l = l.
Proof.
  intros.
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

Lemma set_get_id:
  forall m bid mb
         (HWF:Ir.Memory.wf m)
         (HGET:Ir.Memory.get m bid = Some mb),
    Ir.Memory.set m bid mb = m.
Proof.
  intros.
  unfold Ir.Memory.set.
  unfold Ir.Memory.get in HGET.
  rewrite map_key_In_id.
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
    assert (HNODUP: NoDup (map fst (res))).
    {
      apply lsubseq_NoDup with (l := map fst bs).
      eapply lsubseq_map with (l := bs) (l' := res).
      rewrite HF. eapply lsubseq_filter.
      reflexivity.
      reflexivity.
      assumption.
    }
    eapply NoDup_find_key.
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

(**********************************************
      Lemmas&Theorems about inboundness
 **********************************************)

(* Wellformedness, inversed direction - when a new block is added. *)
Lemma wf_newblk_inv:
  forall mt blocks newblk calltime fresh_cid
         (HWF: wf (mk mt (newblk::blocks) calltime fresh_cid)),
    wf (mk mt blocks calltime fresh_cid).
Proof.
  intros.
  destruct HWF.
  split.
  - intros.
    apply wf_blocks0 with (i := i).
    simpl. simpl in HAS. right. assumption.
  - simpl. simpl in wf_uniqueid0.
    inversion wf_uniqueid0. assumption.
  - unfold alive_P_ranges in *.
    unfold alive_blocks in *.
    simpl in *.
    destruct (MemBlock.alive (snd newblk)) eqn:HALIVE.
    + simpl in wf_disjoint0.
      apply disjoint_ranges_append in wf_disjoint0.
      destruct wf_disjoint0.
      assumption.
    + assumption.
Qed.

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


(* Theorem: there are at most 2 alive blocks
   which have abs_ofs as inbounds. *)
Theorem inbounds_blocks_atmost_2:
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
Theorem inbounds_blocks_forallb:
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

(* Theorem: The results of inbounds_blocks2,
   contain all input offsets. *)
Theorem inbounds_blocks2_forallb2:
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

(* Theorem: all blocks returned by inbounds_blocks2 are alive. *)
Theorem inbounds_blocks2_alive:
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

(* Theorem: inbounds_blocks2 with two different
   elements returns only one block. *)
Theorem inbounds_blocks2_singleton:
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

(* Theorem: inbounds_blocks2 with at least two different
   elements returns only one block. *)
Theorem inbounds_blocks2_singleton2:
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

(* Theorem: if there's alive block blk, which has abs_ofs1 & abs_ofs2
   as its inbounds, blk must be included in the result of inbounds_blocks2. *)
Theorem inbounds_blocks2_In:
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

Theorem inbounds_blocks2_In2:
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


End Memory.

End Ir.
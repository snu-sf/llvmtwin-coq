Require Import Common.
Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import PeanoNat.
Require Import Omega.

Module Ir.

Definition PTRSZ := 16.
Definition MEMSZ := Nat.pow 2 PTRSZ.
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
    @list_incl nat Nat.eq_dec I1 I2 &&
    @list_incl nat Nat.eq_dec I2 I1 &&
    match (cid1, cid2) with
    | (Some c1, Some c2) => Nat.eqb c1 c2
    | (None, None) => true
    | (_, _) => false
    end
  | (_, _) => false
  end.

Inductive blockty :=
| stack | heap | global | function.

Inductive bit :=
| bint: bool -> bit
(* (p, i). Note that 0 <= i < PTRSZ is kept as invariant. *)
| baddr: ptrval -> nat -> bit.

Definition bit0 := bint false.
Definition bit1 := bint true.
Definition bnull (i:nat) := baddr NULL i.

Module Byte.

Structure t := mk
 {b0:bit; b1:bit; b2:bit; b3:bit; b4:bit; b5:bit; b6:bit; b7:bit}.

Definition zero := mk bit0 bit0 bit0 bit0 bit0 bit0 bit0 bit0.
Definition one  := mk bit1 bit0 bit0 bit0 bit0 bit0 bit0 bit0.
Definition mone := mk bit1 bit1 bit1 bit1 bit1 bit1 bit1 bit1.
Definition imax := mk bit0 bit1 bit1 bit1 bit1 bit1 bit1 bit1.
Definition imin := mk bit1 bit0 bit0 bit0 bit0 bit0 bit0 bit0.

Definition null i := mk (bnull (8*i))   (bnull (8*i+1)) (bnull (8*i+2))
                        (bnull (8*i+3)) (bnull (8*i+4)) (bnull (8*i+5))
                        (bnull (8*i+6)) (bnull (8*i+7)).

(* Check whether b has 8 integer bits.
   If it has all integer bits, return the integer bits. *)
Definition getibits (b: Byte.t): option (list bool) :=
  match (b.(b0), b.(b1), b.(b2), b.(b3), b.(b4), b.(b5), b.(b6), b.(b7)) with
  | (bint i0, bint i1, bint i2, bint i3, bint i4, bint i5, bint i6, bint i7) =>
    Some (i0::i1::i2::i3::i4::i5::i6::i7::nil)
  | (_, _, _, _, _, _, _, _) => None
  end.

(* Check whether bs have all integer bits.
   If it have, return the integer. *)
Definition getint (bs: list Byte.t): option N :=
  let bs' := List.map getibits bs in
  let bs2 := List.fold_left
               (fun lowb highb =>
                  match (lowb, highb) with
                  | (None, _) => None
                  | (_, None) => None
                  | (Some lowb, Some highb) => Some (lowb ++ highb)
                  end) bs' (Some nil) in
  match bs2 with
  | None => None
  | Some b => Some (bits_to_N (erase_hzerobits b))
  end.

Eval compute in getibits one.
Eval compute in getint (zero::zero::nil).
Eval compute in getint (one::zero::nil).
Eval compute in getint (zero::one::nil).
Eval compute in getint (one::one::nil).

(* Check whether b has 8 pointer bits (p, i), (p, i + 1, ..)
   If it has, this returns (p, i). *)
Definition getpbits (b: Byte.t): option (ptrval * nat) :=
  match (b.(b0), b.(b1), b.(b2), b.(b3), b.(b4), b.(b5), b.(b6), b.(b7)) with
  | (baddr p0 n0, baddr p1 n1, baddr p2 n2, baddr p3 n3,
     baddr p4 n4, baddr p5 n5, baddr p6 n6, baddr p7 n7) =>
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

Eval compute in getpbits (null 0).
Eval compute in getpbits (null 1).
Eval compute in getptr ((null 0)::nil). (* None *)
Eval compute in getptr ((null 0)::(null 1)::nil). (* Some (pphy (0, nil, None)). *)
Eval compute in getptr ((null 0)::(null 1)::(null 2)::nil). (* None *)

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
    wf_poslen: no_empty_range (P_ranges mb) = true;
    wf_align: forall p (HAS:List.In p mb.(P)), Nat.modulo p mb.(a) = 0;
    wf_inmem: forall p (HAS:List.In p mb.(P)), p + mb.(n) < MEMSZ;
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
  Nat.ltb ofs mb.(n).

Definition inbounds_abs (ofs':nat) (mb:t): bool :=
  in_range ofs' (P0_range mb).

(* offset, len *)
Definition bytes (mb:t) (ofs len:nat): list (Byte.t) :=
  List.firstn len (List.skipn ofs mb.(c)).

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

(* REturns blocks which are alive & has abs_ofss as inbounds. *)
Definition inbounds_blocks_all (m:t) (abs_ofss:list nat)
: list (blockid * MemBlock.t) :=
  snd
    (List.fold_left
       (fun blks_and_ranges abs_ofs =>
          disjoint_include2 blks_and_ranges.(fst) blks_and_ranges.(snd) abs_ofs)
       abs_ofss
       ((alive_P0_ranges m), (alive_blocks m))).

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
  match (List.filter (fun i2 => Nat.eqb i2.(fst) i) m.(blocks)) with
  | nil => None
  | a::b => Some a.(snd)
  end.


Definition incr_time (m:t): t :=
  mk (1 + m.(mt)) m.(blocks) m.(calltimes) m.(fresh_bid).

Definition callbegin (m:t) (cid:callid): t :=
  mk m.(mt) m.(blocks) ((cid, Some m.(mt))::m.(calltimes)) m.(fresh_bid).

Definition callend (m:t) (cid:callid): t :=
  mk m.(mt) m.(blocks) ((cid, None)::m.(calltimes)) m.(fresh_bid).

Definition calltime (m:t) (cid:callid): option time :=
  match (List.filter (fun i2 => Nat.eqb i2.(fst) cid) m.(calltimes)) with
  | nil => None
  | h::t => h.(snd)
  end.


(********************************
             Lemmas
 ********************************)

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

Lemma P_P0_range_lsubseq:
  forall mb (HWF:MemBlock.wf mb),
    lsubseq (MemBlock.P_ranges mb) ((MemBlock.P0_range mb)::nil).
Proof.
  intros.
  unfold MemBlock.P_ranges.
  unfold MemBlock.P0_range.
  destruct (MemBlock.P mb) as [| P0 Pt] eqn:HP1.
  { (* cannot be nil. *)
    assert (List.length (MemBlock.P mb) = 0).
    { rewrite HP1. reflexivity. }
    rewrite (MemBlock.wf_twin) in H. inversion H. assumption.
  }
  unfold MemBlock.addr.
  rewrite HP1. simpl.
  constructor.
  constructor.
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
        apply P_P0_range_lsubseq.
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
   inbounds_blocks_all [ofs]. *)
Lemma inbounds_blocks_inbounds_blocks_all:
  forall (m:t) abs_ofs,
    inbounds_blocks m abs_ofs = inbounds_blocks_all m (abs_ofs::nil).
Proof.
  intros.
  unfold inbounds_blocks.
  unfold inbounds_blocks_all.
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

(* Theorem: inbounds_blocks_all with two different
   elements returns only one block. *)
Theorem inbounds_blocks_all_singleton:
  forall (m:t) (ofs1 ofs2:nat) l (HWF:wf m)
         (HNEQ:~ (ofs1 = ofs2))
         (HINB:inbounds_blocks_all m (ofs1::ofs2::nil) = l),
    List.length l < 2.
Proof.
  intros.
  unfold inbounds_blocks_all in HINB.
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
    rewrite inbounds_blocks_inbounds_blocks_all.
    unfold inbounds_blocks_all.
    simpl.
    rewrite <- HeqP0s.
    rewrite <- Heqmbs.
    rewrite Heqres1.
    reflexivity.
  }
  (* Okay, we showed that inbounds_blocks_all m (ofs1::nil) has
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
    (* show that inbounds_blocks_all m (ofs2::ofs1::nil) has less than
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

(* Theorem: inbounds_blocks_all with at least two different
   elements returns only one block. *)
Theorem inbounds_blocks_all_singleton2:
  forall (m:t) (ofs1 ofs2:nat) l ofs' (HWF:wf m)
         (HNEQ:~ (ofs1 = ofs2))
         (HINB:inbounds_blocks_all m (ofs1::ofs2::ofs') = l),
    List.length l < 2.
Proof.
  intros.
  unfold inbounds_blocks_all in HINB.
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

  assert (res2.(snd) = inbounds_blocks_all m (ofs1::ofs2::nil)).
  {
    unfold inbounds_blocks_all.
    simpl.
    rewrite <- HeqP0.
    rewrite <- Heqblks.
    rewrite <- Heqres1.
    rewrite <- Heqres2.
    reflexivity.
  }
  assert (length (snd res2) < 2).
  {
    apply inbounds_blocks_all_singleton with (m := m) (ofs1 := ofs1) (ofs2 := ofs2).
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


End Memory.

End Ir.
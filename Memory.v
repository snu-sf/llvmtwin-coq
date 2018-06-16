Require Import Common.
Require Import List.
Require Import BinPos.
Require Import Bool.
Require Import PeanoNat.

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
Definition P_size (mb:t):list (nat * nat) :=
  List.map (fun ofs => (ofs, mb.(n))) mb.(P).

(* Returns integer address of the block. *)
Definition addr (mb:t): nat :=
  List.hd 0 mb.(P).

(* Returns (start_ofs, size) of the using one. *)
Definition P0_size (mb:t): nat * nat :=
  (addr mb, mb.(n)).


Structure wf (mb:t) := mkWf
  {
    wf_tcond: forall t (FREED:mb.(r).(snd) = Some t), mb.(r).(fst) < t;
    wf_clen: List.length mb.(c) = mb.(n);
    wf_poslen: mb.(n) <> 0;
    wf_align: forall p (HAS:List.In p mb.(P)), Nat.modulo p mb.(a) = 0;
    wf_inmem: forall p (HAS:List.In p mb.(P)), p + mb.(n) < MEMSZ;
    wf_notnull: forall p (HAS:List.In p mb.(P)), ~ (p = 0);
    wf_disj: disjoint_ranges (P_size mb) = true;
    wf_twin: List.length mb.(P) = TWINCNT
  }.

Definition alive (mb:t): bool :=
  match mb.(r).(snd) with
  | None => true | Some _ => false
  end.

Definition inbounds (mb:t) (ofs:nat): bool :=
  Nat.ltb ofs mb.(n).

Definition inbounds_abs (mb:t) (ofs':nat): bool :=
  in_range ofs' (P0_size mb).

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
  List.concat (List.map (fun b => MemBlock.P_size b.(snd)) (alive_blocks m)).

Definition alive_P0_ranges (m:t): list (nat * nat) :=
  List.map (fun x => MemBlock.P0_size x.(snd)) (alive_blocks m).

(* Returns true if range r never overlaps with other alive blocks,
   false otherwise. *)
Definition allocatable (m:t) (r:list (nat * nat)):bool :=
  disjoint_ranges (r++(alive_P_ranges m)).

(* Returns blocks which are alive & has abs_ofs as inbounds *)
Definition inbounds_blocks (m:t) (abs_ofs:nat): list (blockid * MemBlock.t) :=
  snd (disjoint_include2 (alive_P0_ranges m) (alive_blocks m) abs_ofs).

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

Lemma P_P0_size_lsubseq:
  forall mb (HWF:MemBlock.wf mb),
    lsubseq (MemBlock.P_size mb) ((MemBlock.P0_size mb)::nil).
Proof.
  intros.
  unfold MemBlock.P_size.
  unfold MemBlock.P0_size.
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

(*
Lemma alive_P_P0_ranges:
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
        apply P_P0_size_lsubseq.
        apply wf_blocks with (m := m) (i := newbid).
        rewrite HM.
        apply HWF.
        rewrite HM. simpl. left. reflexivity.
      }
      {
        eapply IHblocks0.
        
      }
    }
    destruct m.

Lemma inbounds_blocks_two:
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
  eapply disjoint_includes_atmost_2.
*)

End Memory.

End Ir.
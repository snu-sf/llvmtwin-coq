Require Import Bool.
Require Import List.
Require Import Omega.
Require Import BinNatDef.
Require Import sflib.
Require Import Sorting.Permutation.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Memory.

Module Ir.


(* The list of dereferenced blocks, given a physical pointer. *)
Definition get_deref_blks_phyptr (m:Ir.Memory.t) (o:nat) (Is:list nat)
           (cid:option Ir.callid) (sz:nat)
: list (Ir.blockid * Ir.MemBlock.t) :=
  match (Ir.Memory.inbounds_blocks2 m (o::(o+sz)::Is)) with
  | nil => nil (* No such block *)
  | blks =>
    match cid with
    | None => blks (* No cid constraint *)
    | Some c =>
      match Ir.Memory.calltime m c with
      | None => blks (* The function is finished. *)
      | Some t => List.filter
                    (fun b => Ir.MemBlock.alive_before t b.(snd))
                    blks
      end
    end
  end.

(* get_deref returns (blockid, block, offset) list which will be dereferenced
   from pointer p and access size sz.
   We'll show that the list of (block, offset) is a singleton later. *)
Definition get_deref (m:Ir.Memory.t) (p:Ir.ptrval) (sz:nat)
: list (Ir.blockid * Ir.MemBlock.t * nat) :=
  match p with
  | Ir.plog bid ofs => (* Logical pointer *)
    match (Ir.Memory.get m bid) with
    | None => nil (* No such block *)
    | Some blk =>
      if Ir.MemBlock.alive blk && Ir.MemBlock.inbounds ofs blk &&
         Ir.MemBlock.inbounds (ofs + sz) blk then
        (bid, blk, ofs)::nil
      else nil
    end
  | Ir.pphy o Is cid => (* Physical pointer *)
    List.map (fun mb => (mb.(fst), mb.(snd), o - Ir.MemBlock.addr mb.(snd)))
             (get_deref_blks_phyptr m o Is cid sz)
  end.

(* Boolean version of get_deref.
   If get_deref returns [], this returns false, true otherwise. *)
Definition deref (m:Ir.Memory.t) (p:Ir.ptrval) (sz:nat): bool :=
  match (get_deref m p sz) with
  | nil => false | _=> true
  end.

(* Returns a list of bytes, after dereferencing p with
   sz bytes. *)
Definition load_bytes (m:Ir.Memory.t) (p:Ir.ptrval) (sz:nat): list Ir.Byte.t :=
  match (get_deref m p sz) with
  | nil => nil
  | (bid, blk, ofs)::_ => Ir.MemBlock.bytes blk ofs sz
  end.

(* Returns a value, after dereferencing p with sz btes. *)
Definition load_val (m:Ir.Memory.t) (p:Ir.ptrval) (t:Ir.ty): Ir.val :=
  let bytes := load_bytes m p (Ir.ty_bytesz t) in
  match t with
  | Ir.ity bitsz =>
    match Ir.Byte.getint bytes bitsz with
    | None => Ir.poison
    | Some n => Ir.num (Nat.modulo (N.to_nat n) (Nat.shiftl 1 bitsz))
    end
  | Ir.ptrty _ =>
    match Ir.Byte.getptr bytes with
    | None => Ir.poison
    | Some p => Ir.ptr p
    end
  end.

(* Store bytes bs into p. *)
Definition store_bytes (m:Ir.Memory.t) (p:Ir.ptrval) (bs:list Ir.Byte.t)
:Ir.Memory.t :=
  match get_deref m p (List.length bs) with
  | nil => m
  | (bid, blk, ofs)::_ =>
    if (Ir.MemBlock.n blk) <? (ofs + length bs) then
      m (* it does not change memory. *)
    else
      Ir.Memory.set m bid (Ir.MemBlock.set_bytes blk ofs bs)
  end.

(* Store value v into p. *)
Definition store_val (m:Ir.Memory.t) (p:Ir.ptrval) (v:Ir.val) (t:Ir.ty)
: Ir.Memory.t :=
  match (t, v) with
  | (Ir.ity bitsz, Ir.num n) =>
    let bs := Ir.Byte.ofint (N.of_nat n) bitsz in
    if (Ir.ty_bytesz (Ir.ity bitsz)) =? List.length bs then
      store_bytes m p bs
    else m (* Wrongly typed. *)
  | (Ir.ptrty pty, Ir.ptr pv) =>
    let bs := Ir.Byte.ofptr pv in
    if (Ir.ty_bytesz (Ir.ptrty pty)) =? List.length bs then
      store_bytes m p bs
    else m (*Wrongly typed*)
  | _ => m (*Wrongly typed*)
  end.

(* Convert a logical pointer to physical pointer. *)
Definition log_to_phy (m:Ir.Memory.t) (bid:Ir.blockid) (ofs:nat): option Ir.ptrval :=
  match Ir.Memory.get m bid with
  | None => None
  | Some bb => Some (Ir.pphy
     (Nat.modulo (Ir.MemBlock.addr bb + ofs) Ir.MEMSZ)
                    nil
                    None)
  end.

(* Convert a pointer to physical pointer. *)
Definition ptr_to_phy (m:Ir.Memory.t) (p:Ir.ptrval): option Ir.ptrval :=
  match p with
  | Ir.plog bid ofs => log_to_phy m bid ofs
  | Ir.pphy o Is cid => Some (Ir.pphy o nil None)
  end.



(***********************************************
            Lemmas about get_deref
 ***********************************************)

(* get_deref log(bid, ofs) either returns the input (bid, block, ofs)
   or returns nothing. *)
Lemma get_deref_log:
  forall (m:Ir.Memory.t) bid ofs sz bos blk
         (HDEREF: get_deref m (Ir.plog bid ofs) sz = bos)
         (HBLK: Ir.Memory.get m bid = Some blk),
    bos = (bid, blk, ofs)::nil \/ bos = nil.
Proof.
  intros.
  unfold get_deref in HDEREF.
  rewrite HBLK in HDEREF.
  destruct (Ir.MemBlock.alive blk && Ir.MemBlock.inbounds ofs blk &&
            Ir.MemBlock.inbounds (ofs + sz) blk).
  - left. congruence.
  - right. congruence.
Qed.

Lemma get_deref_log_inv:
  forall (m:Ir.Memory.t) bid ofs sz blk
         (HDEREF: exists e, get_deref m (Ir.plog bid ofs) sz = e::nil)
         (HBLK: Ir.Memory.get m bid = Some blk),
    Ir.MemBlock.alive blk &&
    Ir.MemBlock.inbounds ofs blk &&
    Ir.MemBlock.inbounds (ofs + sz) blk = true.
Proof.
  intros.
  remember (Ir.MemBlock.alive blk) as b1.
  remember (Ir.MemBlock.inbounds ofs blk) as b2.
  remember (Ir.MemBlock.inbounds (ofs + sz) blk) as b3.
  destruct HDEREF as [bo HDEREF].
  unfold get_deref in HDEREF.
  rewrite HBLK in HDEREF.
  rewrite <- Heqb1,<- Heqb2, <- Heqb3 in HDEREF.
  destruct b1; destruct b2 ; destruct b3; simpl in HDEREF; try (inversion HDEREF; fail).
  reflexivity.
Qed.

Lemma get_deref_log_alive:
  forall m l o p mb sz
         (HGET:Some mb = Ir.Memory.get m l)
         (HDEREF:Ir.get_deref m (Ir.plog l o) sz = [p]),
    Ir.MemBlock.alive mb = true.
Proof.
  intros.
  assert (exists p, Ir.get_deref m (Ir.plog l o) sz = [p]).
  { eexists. rewrite HDEREF. reflexivity. }
  eapply Ir.get_deref_log_inv in H.
  2: rewrite <- HGET. 2: reflexivity.
  rewrite andb_true_iff in H.
  destruct H.
  rewrite andb_true_iff in H.
  intuition.
Qed.

Lemma get_deref_inv:
  forall (m:Ir.Memory.t) p bid ofs sz blk
         (HSZ:sz > 0)
         (HWF:Ir.Memory.wf m)
         (HDEREF: get_deref m p sz = (bid, blk, ofs)::nil)
         (HBLK: Ir.Memory.get m bid = Some blk),
    Ir.MemBlock.alive blk &&
    Ir.MemBlock.inbounds ofs blk &&
    Ir.MemBlock.inbounds (ofs + sz) blk = true.
Proof.
  intros.
  destruct p as [b n | o Is cid].
  - apply get_deref_log_inv with (m := m) (bid := bid).
    assert (b = bid /\ n = ofs).
    { unfold get_deref in HDEREF.
      destruct (Ir.Memory.get m b).
      destruct (Ir.MemBlock.alive t && Ir.MemBlock.inbounds n t &&
                                  Ir.MemBlock.inbounds (n + sz) t).
      inversion HDEREF. split; reflexivity.
      inversion HDEREF. inversion HDEREF. }
    destruct H as [H1 H2]. rewrite H1, H2 in HDEREF.
    exists (bid, blk, ofs). assumption.
    assumption.
  - unfold get_deref in HDEREF.
    unfold get_deref_blks_phyptr in HDEREF.
    remember (Ir.Memory.inbounds_blocks2 m (o::o+sz::Is)) as res.
    symmetry in Heqres.
    assert (HFORALL := Ir.Memory.inbounds_blocks2_forallb2 m
               (o::o+sz::Is) res Heqres).
    simpl in HFORALL.
    assert (List.length res < 2).
    { apply Ir.Memory.inbounds_blocks2_singleton2 with (m := m)
          (ofs1 := o) (ofs2 := o+sz) (ofs' := Is).
      assumption.
      apply Nat.lt_neq.
      apply Nat.lt_add_pos_r. assumption.
      assumption. }
    destruct res.
    + simpl in HDEREF. inversion HDEREF.
    + destruct res.
      {
        destruct cid.
        {
          remember (Ir.Memory.calltime m c) as t'.
          destruct t'.
          {
            simpl in HDEREF.
            destruct p.
            {
              simpl in *.              
              destruct (Ir.MemBlock.alive_before t t0) eqn:HAB.
              {
                simpl in HDEREF.
                inversion HDEREF.
                rewrite H1, H2, H3 in *. clear H1 H2.
                repeat (rewrite andb_true_r in HFORALL).
                repeat (rewrite andb_true_iff in HFORALL).
                destruct HFORALL as [HFORALL1 [HFORALL2 HFORALL3]].
                assert (HFORALL1' := HFORALL1).
                rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs) in HFORALL1.
                rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs + sz) in HFORALL2.
                rewrite HFORALL1, HFORALL2.
                assert (HALIVE: List.forallb (fun b=> Ir.MemBlock.alive b.(snd))
                                             ((bid, blk)::nil) = true).
                { eapply Ir.Memory.inbounds_blocks2_alive.
                  eassumption. }
                simpl in HALIVE. rewrite HALIVE. reflexivity.
                rewrite Ir.MemBlock.inbounds_abs_addr
                  with (o := o) (blk := blk) (ofs := ofs).
                omega. assumption. assumption.
                rewrite Nat.add_comm.
                apply Ir.MemBlock.inbounds_abs_addr; assumption.
              }
              { simpl in HDEREF. inversion HDEREF. }
            }
          }
          { destruct p.
            simpl in *.
            simpl in HDEREF.
            inversion HDEREF.
            rewrite H1, H2, H3 in *. clear H1 H2.
            repeat (rewrite andb_true_r in HFORALL).
            repeat (rewrite andb_true_iff in HFORALL).
            destruct HFORALL as [HFORALL1 [HFORALL2 HFORALL3]].
            assert (HFORALL1' := HFORALL1).
            rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs) in HFORALL1.
            rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs + sz) in HFORALL2.
            rewrite HFORALL1, HFORALL2.
            assert (HALIVE: List.forallb (fun b=> Ir.MemBlock.alive b.(snd))
                                         ((bid, blk)::nil) = true).
            { eapply Ir.Memory.inbounds_blocks2_alive.
              eassumption. }
            simpl in HALIVE. rewrite HALIVE. reflexivity.
            rewrite Ir.MemBlock.inbounds_abs_addr
              with (o := o) (blk := blk) (ofs := ofs).
            omega. assumption. assumption.
            rewrite Nat.add_comm.
            apply Ir.MemBlock.inbounds_abs_addr; assumption.
          }
        }
        { destruct p.
          simpl in *.
          simpl in HDEREF.
          inversion HDEREF.
          rewrite H1, H2, H3 in *. clear H1 H2.
          repeat (rewrite andb_true_r in HFORALL).
          repeat (rewrite andb_true_iff in HFORALL).
          destruct HFORALL as [HFORALL1 [HFORALL2 HFORALL3]].
          assert (HFORALL1' := HFORALL1).
          rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs) in HFORALL1.
          rewrite <- Ir.MemBlock.inbounds_inbounds_abs with (ofs := ofs + sz) in HFORALL2.
          rewrite HFORALL1, HFORALL2.
          assert (HALIVE: List.forallb (fun b=> Ir.MemBlock.alive b.(snd))
                                       ((bid, blk)::nil) = true).
          { eapply Ir.Memory.inbounds_blocks2_alive.
            eassumption. }
          simpl in HALIVE. rewrite HALIVE. reflexivity.
          rewrite Ir.MemBlock.inbounds_abs_addr
            with (o := o) (blk := blk) (ofs := ofs).
          omega. assumption. assumption.
          rewrite Nat.add_comm.
          apply Ir.MemBlock.inbounds_abs_addr; assumption.
        } 
      }
      { simpl in H.
        omega.
      }
Qed.


(* Lemma: get_deref_blks_byaddrs returns at most one alive block. *)
Lemma get_deref_blks_phyptr_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) o Is cid sz bos
         (HSZ: 0 < sz)
         (HDEREF: get_deref_blks_phyptr m o Is cid sz = bos),
  (exists bo, bos = bo::nil /\ Ir.Memory.get m bo.(fst) = Some bo.(snd))
  \/ (bos = nil).
Proof.
  intros.
  unfold get_deref_blks_phyptr in HDEREF.
  remember (Ir.Memory.inbounds_blocks2 m (o::o+sz::Is)) as blks.
  assert (List.length blks < 2).
  {
    apply (Ir.Memory.inbounds_blocks2_singleton2 m o (o+sz) blks Is).
    assumption.
    intros H.
    destruct sz.
    - inversion HSZ.
    - rewrite PeanoNat.Nat.add_succ_r in H.
      rewrite PeanoNat.Nat.add_comm in H.
      apply PeanoNat.Nat.succ_add_discr in H.
      assumption.
    - congruence.
  }
  destruct blks as [| b1 blks].
  { right. simpl in HDEREF. congruence. }
  simpl in H.
  destruct blks as [| b2 blks].
  {
    destruct cid as [cid |].
    - destruct (Ir.Memory.calltime m cid) as [cid' |] eqn:HCT.
      + simpl in HDEREF.
        destruct (Ir.MemBlock.alive_before cid' (snd b1)).
        * left. eexists. split.
          rewrite HDEREF. reflexivity.
          eapply Ir.Memory.blocks_get. assumption. reflexivity.
          eapply Ir.Memory.inbounds_blocks2_In2.
          eassumption.
        * right. congruence.
      + left. eexists. rewrite HDEREF.
        split. reflexivity.
        eapply Ir.Memory.blocks_get. assumption. reflexivity.
        eapply Ir.Memory.inbounds_blocks2_In2. eassumption.
    - left. eexists. rewrite HDEREF.
      split. reflexivity. eapply Ir.Memory.blocks_get. assumption. reflexivity.
      eapply Ir.Memory.inbounds_blocks2_In2. eassumption.
  }
  {
    simpl in H.
    assert (S (S (length blks)) = 2 + length blks). (* -_-; *)
    { reflexivity. }
    rewrite H0 in H.
    apply Lt.lt_not_le in H.
    exfalso.
    apply H.
    apply PeanoNat.Nat.le_add_r.
  }
Qed.

Lemma get_deref_phy_nil_same:
  forall m1 m2 bid mb bwid o cid ofs
         (HGET:Some mb = Ir.Memory.get m1 bid)
         (HWF1:Ir.Memory.wf m1)
         (HWF2:Ir.Memory.wf m2)
         (HSAME:Ir.Memory.get m1 bid = Ir.Memory.get m2 bid)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m1 (Ir.pphy o nil cid) bwid = (bid, mb, ofs)::nil)
         (HCALLTIME:Ir.Memory.calltimes m1 = Ir.Memory.calltimes m2),
    Ir.get_deref m1 (Ir.pphy o nil cid) bwid =
    Ir.get_deref m2 (Ir.pphy o nil cid) bwid.
Proof.
  intros.
  unfold Ir.get_deref.
  unfold Ir.get_deref_blks_phyptr.
  assert (Ir.Memory.inbounds_blocks2 m1 [o; o + bwid] =
            Ir.Memory.inbounds_blocks2 m2 [o; o + bwid]).
  { eapply Ir.Memory.inbounds_blocks2_same; try eassumption.
    remember (Ir.Memory.inbounds_blocks2 m1 [o; o + bwid]) as l.
    symmetry in Heql.
    dup Heql.
    apply Ir.Memory.inbounds_blocks2_singleton in Heql0.
    unfold Ir.get_deref in HDEREF.
    unfold Ir.get_deref_blks_phyptr in HDEREF.
    rewrite Heql in HDEREF.
    destruct l.
    { inv HDEREF. }
    { destruct l.
      { des_ifs. simpl in HDEREF. des_ifs. simpl in HDEREF. inv HDEREF.
        destruct p. reflexivity.
        simpl in HDEREF. inv HDEREF. destruct p. reflexivity.
        simpl in HDEREF. inv HDEREF. destruct p. reflexivity.
      }
      { simpl in Heql0. omega. }
    }
    assumption. omega.
  }
  rewrite H.
  destruct (Ir.Memory.inbounds_blocks2 m2 [o; o + bwid]); try reflexivity.
  destruct cid; try reflexivity.
  unfold Ir.Memory.calltime. rewrite HCALLTIME.
  des_ifs.
Qed.

Lemma get_deref_phy_I_cons:
  forall m bid mb bwid o cid ofs I i
         (HGET:Some mb = Ir.Memory.get m bid)
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o I cid) bwid = (bid, mb, ofs)::nil),
    (in_range i (Ir.MemBlock.P0_range mb) = true ->
     Ir.get_deref m (Ir.pphy o (i::I) cid) bwid = (bid, mb, ofs)::nil) /\
    (in_range i (Ir.MemBlock.P0_range mb) = false ->
     Ir.get_deref m (Ir.pphy o (i::I) cid) bwid = nil).
Proof.
  intros.
  unfold Ir.get_deref in *.
  unfold Ir.get_deref_blks_phyptr in *.
  remember (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I)) as inbs1.
  remember (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: i :: I)) as inbs2.
  assert (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: i :: I) =
          Ir.Memory.inbounds_blocks2 m (i :: o :: o + bwid :: I)).
  { eapply Ir.Memory.inbounds_blocks2_Permutation with (I := i::o::(o+bwid)::I).
    apply perm_trans with (l' := o::i::o+bwid::I).
    constructor. apply perm_skip. constructor.
    reflexivity. }
  rewrite H in *. clear H.
  dup Heqinbs1. (* make sigleton *)
  symmetry in Heqinbs0.
  apply Ir.Memory.inbounds_blocks2_singleton2 in Heqinbs0.
  destruct inbs1. inv HDEREF.
  destruct inbs1; try (simpl in Heqinbs0; omega).
  (* okay, it is singleton. *)
  dup Heqinbs1.
  symmetry in Heqinbs1.
  destruct p.
  apply Ir.Memory.inbounds_blocks2_cons with (i := i) in Heqinbs1.
  destruct Heqinbs1.
  (* okay, let's destruct cid now. *)
  destruct cid.
  { destruct (Ir.Memory.calltime m c) eqn:HCT.
    { simpl in HDEREF.
      destruct (Ir.MemBlock.alive_before t0 t) eqn:HALIVE.
      { (* okay, ready. *)
        simpl in HDEREF. inv HDEREF.
        split.
        { (* inbounds *)
          intros HINB. apply H in HINB. rewrite HINB.
          simpl. rewrite HALIVE. simpl. reflexivity. }
        { (* ot inbounds *)
          intros HNOTINB. apply H0 in HNOTINB. rewrite HNOTINB.
          reflexivity. }
      }
      { (* okay, ready. *)
        simpl in HDEREF. inv HDEREF. }
    }
    {
      simpl in HDEREF. inv HDEREF.
      split.
      { (* inbounds *)
        intros HINB. apply H in HINB. rewrite HINB.
        simpl. reflexivity. }
      { (* ot inbounds *)
        intros HNOTINB. apply H0 in HNOTINB. rewrite HNOTINB.
        reflexivity. }
    }
  }
  {
    simpl in HDEREF. inv HDEREF.
    split.
    { (* inbounds *)
      intros HINB. apply H in HINB. rewrite HINB.
      simpl. reflexivity. }
    { (* ot inbounds *)
      intros HNOTINB. apply H0 in HNOTINB. rewrite HNOTINB.
      reflexivity. }
  }
  assumption.
  omega.
Qed.

Lemma get_deref_phy_I_cons2:
  forall m bwid o cid I i
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o I cid) bwid = nil),
     Ir.get_deref m (Ir.pphy o (i::I) cid) bwid = nil.
Proof.
  intros.
  unfold Ir.get_deref in *.
  unfold Ir.get_deref_blks_phyptr in *.
  assert ( Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: i :: I) =
           Ir.Memory.inbounds_blocks2 m (i :: o :: o + bwid :: I)).
  { apply Ir.Memory.inbounds_blocks2_Permutation with (I := i::o::o+bwid::I).
    eapply perm_trans. eapply perm_swap. eapply perm_skip.
    eapply perm_swap. reflexivity. }
  rewrite H in *. clear H.

  destruct (Ir.Memory.inbounds_blocks2 m (o::o+bwid::I)) eqn:Hib2.
  { apply Ir.Memory.inbounds_blocks2_cons2 with (i := i) in Hib2. rewrite Hib2.
    reflexivity.
  }
  { dup Hib2.
    apply Ir.Memory.inbounds_blocks2_singleton2 in Hib0; try congruence; try omega.
    destruct l; try (simpl in Hib0; omega).
    destruct p.
    apply Ir.Memory.inbounds_blocks2_cons with (i := i) in Hib2.
    destruct Hib2.
    destruct (in_range i (Ir.MemBlock.P0_range t)).
    { exploit H. reflexivity. intros HH. rewrite HH.
      rewrite HDEREF. reflexivity. }
    { exploit H0. reflexivity. intros HH. rewrite HH.
      reflexivity. }
  }
Qed.
  
Lemma get_deref_phy_I:
  forall m bid mb bwid o cid ofs I
         (HGET:Some mb = Ir.Memory.get m bid)
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o nil cid) bwid = (bid, mb, ofs)::nil),
    Ir.get_deref m (Ir.pphy o I cid) bwid = (bid, mb, ofs)::nil \/
    Ir.get_deref m (Ir.pphy o I cid) bwid = nil.
Proof.
  induction I.
  { intros. left. assumption. }
  { intros. exploit IHI; try assumption. intros HH.
    destruct HH.
    { eapply get_deref_phy_I_cons with (i := a) in H; try assumption.
      destruct H.
      destruct (in_range a (Ir.MemBlock.P0_range mb)) eqn:HIN.
      { exploit H. reflexivity. intros. left. assumption. }
      { exploit H0. reflexivity. intros. right. assumption. }
    }
    { right.
      eapply get_deref_phy_I_cons2 in H; eassumption.
    }
  }
Qed.

Lemma get_deref_phy_I2:
  forall m bwid o cid I
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o nil cid) bwid = nil),
    Ir.get_deref m (Ir.pphy o I cid) bwid = nil.
Proof.  induction I.
  { intros. assumption. }
  { intros. exploit IHI; try assumption. intros HH.
    eapply get_deref_phy_I_cons2 with (i := a) in HH; try assumption.
  }
Qed.

Lemma get_deref_phy_I3:
  forall m bid mb bwid o ofs I
         (HGET:Some mb = Ir.Memory.get m bid)
         (HALIVE:Ir.MemBlock.alive mb = true)
         (HWF:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o nil None) bwid = [(bid, mb, ofs)])
         (HFORALLB:List.forallb (fun i => Ir.MemBlock.inbounds_abs i mb) I = true),
  Ir.get_deref m (Ir.pphy o I None) bwid = [(bid, mb, ofs)].
Proof.
  intros.
  unfold Ir.get_deref in *.
  unfold Ir.get_deref_blks_phyptr in *.
  destruct (Ir.Memory.inbounds_blocks2 m [o; o + bwid]) eqn:HINB; try simpl in HDEREF;
    try congruence.
  destruct p.
  simpl in *.
  destruct l; simpl in HDEREF; try (inv HDEREF; fail).
  inv HDEREF.
  assert (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I) = [(bid, mb)]).
  { eapply Ir.Memory.inbounds_blocks2_singleton4; try assumption.
    omega.
    simpl.
    simpl in HINB.
    apply Ir.Memory.inbounds_blocks2_forallb2 in HINB.
    simpl in HINB.
    repeat (rewrite andb_true_r in HINB).
    rewrite andb_true_iff in HINB.
    destruct HINB.
    rewrite H. rewrite H0.
    simpl. assumption.
  }
  rewrite H. simpl. reflexivity.
Qed.

Lemma get_deref_phy_I_subseq:
  forall m bid mb bwid o ofs I1 I2
         (HGET:Some mb = Ir.Memory.get m bid)
         (HWF:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HLSS:lsubseq I1 I2)
         (HDEREF:Ir.get_deref m (Ir.pphy o I1 None) bwid = [(bid, mb, ofs)]),
      Ir.get_deref m (Ir.pphy o I2 None) bwid = [(bid, mb, ofs)].
Proof.
  intros.
  unfold Ir.get_deref in *.
  unfold Ir.get_deref_blks_phyptr in *.
  remember (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I1)) as blks1.
  remember (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I2)) as blks2.
  symmetry in Heqblks1.
  symmetry in Heqblks2.
  dup Heqblks1.
  apply Ir.Memory.inbounds_blocks2_singleton2 in Heqblks1; try assumption; try omega.
  destruct blks1. ss.
  destruct blks1; simpl in HDEREF; try (inv HDEREF; fail).
  destruct p. simpl in HDEREF. inversion HDEREF. subst b. subst t. subst ofs.
  clear HDEREF.
  dup Heqblks0.
  eapply Ir.Memory.inbounds_blocks2_forallb2 in Heqblks3.
  simpl in Heqblks3.
  repeat (rewrite andb_true_r in Heqblks3).
  rewrite andb_true_iff in Heqblks3. destruct Heqblks3.
  rewrite andb_true_iff in H0. destruct H0.
  assert (lsubseq blks2 [(bid, mb)]).
  { eapply Ir.Memory.inbounds_blocks2_lsubseq2.
    eassumption.
    eassumption.
    constructor. constructor. assumption. }
  apply Ir.Memory.inbounds_blocks2_singleton2 in Heqblks2; try assumption; try omega.
  destruct blks2. inv H2.
  destruct blks2.
  inv H2. reflexivity.
  inv H6.
  simpl in Heqblks2. omega.
Qed.

Lemma get_deref_phy_cid:
  forall m bid mb bwid o cid ofs I
         (HGET:Some mb = Ir.Memory.get m bid)
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o I None) bwid = (bid, mb, ofs)::nil),
    Ir.get_deref m (Ir.pphy o I cid) bwid = (bid, mb, ofs)::nil \/
    Ir.get_deref m (Ir.pphy o I cid) bwid = nil.
Proof.
  intros.
  unfold get_deref in *.
  unfold get_deref_blks_phyptr in *.
  destruct (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I)) eqn:HH;
    try (inv HDEREF; fail).
  simpl in HDEREF.
  destruct l; try (inv HDEREF; fail).
  simpl in HDEREF. inv HDEREF.
  destruct cid.
  { destruct (Ir.Memory.calltime m c).
    { simpl.
      destruct (Ir.MemBlock.alive_before t (snd p)).
      { simpl. left. reflexivity. }
      { right. reflexivity. }
    }
    { left. simpl. reflexivity. }
  }
  { left. reflexivity. }
Qed.

Lemma get_deref_phy_cid2:
  forall m bwid o cid I
         (HWF1:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o I None) bwid = nil),
    Ir.get_deref m (Ir.pphy o I cid) bwid = nil.
Proof.
  intros.
  unfold get_deref in *.
  unfold get_deref_blks_phyptr in *.
  destruct (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I)) eqn:HH;
    try (inv HDEREF; fail).
  reflexivity.
Qed.

Lemma get_deref_phy_cid3:
  forall m bid mb bwid o cid ofs I
         (HGET:Some mb = Ir.Memory.get m bid)
         (HWF:Ir.Memory.wf m)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m (Ir.pphy o I cid) bwid = [(bid, mb, ofs)]),
      Ir.get_deref m (Ir.pphy o I None) bwid = [(bid, mb, ofs)].
Proof.
  intros.
  unfold Ir.get_deref in *.
  unfold Ir.get_deref_blks_phyptr in *.
  remember (Ir.Memory.inbounds_blocks2 m (o :: o + bwid :: I)) as blks.
  symmetry in Heqblks.
  apply Ir.Memory.inbounds_blocks2_singleton2 in Heqblks; try assumption; try omega.
  destruct blks. ss.
  destruct blks.
  des_ifs.
  simpl in HDEREF. des_ifs.
  simpl in Heqblks. omega.
Qed.

Lemma get_deref_blks_phyptr_inbounds_blocks2:
  forall b t m o Is cid sz
         (HIN:List.In (b, t) (Ir.get_deref_blks_phyptr m o Is cid sz)),
    List.In (b, t) (Ir.Memory.inbounds_blocks2 m (o::o+sz::Is)).
Proof.
  intros.
  unfold Ir.get_deref_blks_phyptr in HIN.
  des_ifs.
  { eapply List.filter_In. eassumption. }
Qed.

Lemma get_deref_phy_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) o Is cid (sz:nat) bos
         (HSZ: 0 < sz)
         (HDEREF: Ir.get_deref m (Ir.pphy o Is cid) sz = bos),
  (exists bo, bos = bo::nil /\
              Ir.Memory.get m bo.(fst).(fst) = Some bo.(fst).(snd) /\
              o = Ir.MemBlock.addr (bo.(fst).(snd)) + (bo.(snd)))
  \/ (bos = nil).
Proof.
  intros.
  unfold Ir.get_deref in HDEREF.
  remember (Ir.get_deref_blks_phyptr m o Is cid sz) as blks.
  assert ((exists bo0, blks = bo0::nil /\
                       Ir.Memory.get m bo0.(fst) = Some bo0.(snd))
          \/ (blks = nil)).
  { eapply Ir.get_deref_blks_phyptr_singleton.
    eassumption.
    eassumption.
    rewrite <- Heqblks. reflexivity. }
  destruct H.
  { destruct H.
    destruct H.
    rewrite H in HDEREF.
    simpl in HDEREF.
    left. eexists. split. rewrite <- HDEREF.
    reflexivity. simpl.
    split. assumption.
    destruct x. simpl in *.
    assert (Ir.MemBlock.addr t <= o).
    { assert (List.In (b, t) blks).
      { rewrite H. simpl. left. reflexivity. }
      rewrite Heqblks in H1.
      apply get_deref_blks_phyptr_inbounds_blocks2 in H1.
      remember (Ir.Memory.inbounds_blocks2 m (o :: o + sz :: Is)) as lt.
      symmetry in Heqlt.
      dup Heqlt.
      apply In_pair_split_snd in H1.
      apply Ir.Memory.inbounds_blocks2_forallb in Heqlt.
      eapply forallb_In in Heqlt; try eassumption.
      eapply Ir.MemBlock.inbounds_abs_addr in Heqlt. omega. reflexivity.
    }
    omega.
  }
  { right. rewrite H in HDEREF. simpl in HDEREF. congruence. }
Qed.

(* Theorem: get_deref always returns at most one block. *)
Theorem get_deref_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) (p:Ir.ptrval) (sz:nat) bos
         (HSZ: 0 < sz)
         (HDEREF: get_deref m p sz = bos),
  (exists bo, bos = bo::nil /\ Ir.Memory.get m bo.(fst).(fst) = Some bo.(fst).(snd))
  \/ (bos = nil).
Proof.
  intros.
  destruct p as [bid ofs | o Is cid].
  - (* logical ptr *)
    unfold get_deref in HDEREF.
    destruct (Ir.Memory.get m bid) eqn:HGET.
    remember (Ir.MemBlock.alive t && Ir.MemBlock.inbounds ofs t &&
              Ir.MemBlock.inbounds (ofs + sz) t) as cond in HDEREF.
    destruct cond; rewrite <- HDEREF.
    + left. eexists. split. reflexivity.
      simpl. assumption.
    + right. reflexivity.
    + right. congruence.
  - unfold get_deref in HDEREF.
    remember (get_deref_blks_phyptr m o Is cid sz) as blks.
    assert ((exists bo0, blks = bo0::nil /\
                         Ir.Memory.get m bo0.(fst) = Some bo0.(snd))
            \/ (blks = nil)).
    { eapply get_deref_blks_phyptr_singleton.
      eassumption.
      eassumption.
      rewrite <- Heqblks. reflexivity. }
    destruct H.
    { destruct H.
      destruct H.
      rewrite H in HDEREF.
      simpl in HDEREF.
      left. eexists. split. rewrite <- HDEREF.
      reflexivity. simpl. assumption.
    }
    right. rewrite H in HDEREF. simpl in HDEREF. congruence.
Qed.

Lemma get_deref_phy_same:
  forall m1 m2 bid mb bwid o cid ofs I
         (HGET:Some mb = Ir.Memory.get m1 bid)
         (HWF1:Ir.Memory.wf m1)
         (HWF2:Ir.Memory.wf m2)
         (HSAME:Ir.Memory.get m1 bid = Ir.Memory.get m2 bid)
         (HSZ:bwid > 0)
         (HDEREF:Ir.get_deref m1 (Ir.pphy o I cid) bwid = (bid, mb, ofs)::nil)
         (HCALLTIME:Ir.Memory.calltimes m1 = Ir.Memory.calltimes m2),
    Ir.get_deref m1 (Ir.pphy o I cid) bwid =
    Ir.get_deref m2 (Ir.pphy o I cid) bwid.
Proof.
  intros.
  induction I.
  { eapply get_deref_phy_nil_same; try eassumption. }
  { remember (Ir.get_deref m1 (Ir.pphy o I cid) bwid) as bb.
    symmetry in Heqbb.
    dup Heqbb.
    apply get_deref_singleton in Heqbb.
    destruct Heqbb.
    { (* get m1 (fst (fst bo)) is [x]. *)
      destruct H. destruct H.
      destruct bb. inv H.
      destruct bb.
      { inv H.
        destruct x. destruct p. simpl in H0.
        apply get_deref_phy_I_cons with (i := a) in Heqbb0; try congruence.
        destruct Heqbb0.
        destruct (in_range a (Ir.MemBlock.P0_range t)) eqn:HINR.
        { exploit H. reflexivity. intros HH.
          dup HDEREF. rewrite HH in HDEREF0. inv HDEREF0.
          rewrite HDEREF.
          exploit IHI. reflexivity. intros HH'. symmetry in HH'.
          apply get_deref_phy_I_cons with (i := a) in HH'; try congruence.
          destruct HH'. rewrite H2. reflexivity. congruence.
        }
        { exploit H1. reflexivity. intros HH.
          dup HDEREF. rewrite HH in HDEREF0. inv HDEREF0. }
      }
      { inv H. }
    }
    { rewrite H in Heqbb0.
      eapply get_deref_phy_I_cons2 with (i := a) in Heqbb0; try eassumption.
      congruence.
    }
    { eassumption. }
    { omega. }
  }
Qed.

Lemma get_deref_ofs_lt_MEMSZ:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) p sz bid mb ofs
         (HSZ:0 < sz)
         (HDEREF:get_deref m p sz = (bid, mb, ofs)::nil),
    Ir.MemBlock.addr mb + ofs < Ir.MEMSZ.
Proof.
  intros.
  assert (HS := get_deref_singleton m m_wf p sz ((bid, mb, ofs)::nil) HSZ HDEREF).
  destruct HS.
  - destruct H.
    destruct H.
    inversion H.
    destruct x.
    destruct p0.
    inversion H2.
    rewrite <- H3, <- H4, <- H5 in *. clear H3 H4 H5.
    simpl in H0.
    (* Now we have Ir.Memory.get m bid = Some mb. *)
    assert (HINV := get_deref_inv m p bid ofs sz mb HSZ m_wf HDEREF H0).
    rewrite andb_true_iff in HINV.
    rewrite andb_true_iff in HINV.
    destruct HINV as [[HINV1 HINV2] HINV3].
    assert (Ir.MemBlock.addr mb + Ir.MemBlock.n mb < Ir.MEMSZ).
    {
      assert (Ir.MemBlock.wf mb).
      { eapply Ir.Memory.wf_blocks.
        eassumption.
        eapply Ir.Memory.get_In. symmetry. eassumption. reflexivity. }
      apply Ir.MemBlock.wf_inmem.
      { assumption. }
      unfold Ir.MemBlock.addr.
      remember (Ir.MemBlock.P mb) as Ps.
      assert (List.length Ps = Ir.TWINCNT).
      { rewrite HeqPs. apply Ir.MemBlock.wf_twin. assumption. }
      destruct Ps.
      { simpl in H3. inversion H3. }
      { simpl. auto. }
    }
    assert (ofs < Ir.MemBlock.n mb).
    { unfold Ir.MemBlock.inbounds in HINV3.
      rewrite Nat.leb_le in HINV3.
      omega. }
    omega.
  - inversion H.
Qed.
  

(* Theorem: A logical pointer (bid, ofs) and a
   physical pointer which is converted from (bid, ofs) both
   access a same memory block with same offset, if
   access size is larger than zero. *)
Theorem get_deref_ptr_phy_same:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) p p' (sz:nat) bo
         (HSZ: 0 < sz)
         (HDEREF: get_deref m p sz = bo::nil)
         (HP':ptr_to_phy m p  = Some p'),
    get_deref m p' sz = bo::nil.
Proof.
  intros.
  destruct p as [bid ofs | o Is cid].
  {
    unfold ptr_to_phy in HP'.
    unfold log_to_phy in HP'.
    remember (Ir.Memory.get m bid) as blk.
    symmetry in Heqblk.
    destruct blk as [blk | ].
    + remember (Ir.MemBlock.alive blk) as alive.
      remember (Ir.MemBlock.inbounds ofs blk) as inb1.
      remember (Ir.MemBlock.inbounds (ofs + sz) blk) as inb2.
      assert (HLOG := get_deref_log m bid ofs sz (bo::nil) blk HDEREF Heqblk).
      destruct HLOG as [HLOG | HLOG]; try (inversion HLOG; fail).
      inversion HLOG. rewrite H0 in *. clear H0 HLOG.
      assert (HMOD: (Ir.MemBlock.addr blk + ofs) mod Ir.MEMSZ =
                    Ir.MemBlock.addr blk + ofs).
      { apply Nat.mod_small.
        destruct bo. destruct p.
        eapply get_deref_ofs_lt_MEMSZ.
        eassumption. eassumption. eassumption. }
      rewrite HMOD in HP'.
      inversion HP'.
      assert (HCOND: Ir.MemBlock.alive blk && Ir.MemBlock.inbounds ofs blk &&
                                       Ir.MemBlock.inbounds (ofs + sz) blk = true).
      {
        eapply get_deref_log_inv.
        eexists.
        apply HDEREF.
        assumption.
      }
      rewrite <- Heqalive, <- Heqinb1, <- Heqinb2 in HCOND.
      destruct alive; destruct inb1; destruct inb2;
        simpl in HCOND; try (inversion HCOND; fail).
      rewrite Ir.MemBlock.inbounds_inbounds_abs
        with (ofs_abs := Ir.MemBlock.addr blk + ofs)
        in Heqinb1.
      rewrite Ir.MemBlock.inbounds_inbounds_abs
        with (ofs_abs := Ir.MemBlock.addr blk + ofs + sz)
        in Heqinb2.
      unfold get_deref.
      unfold get_deref_blks_phyptr.
      remember (Ir.Memory.inbounds_blocks2 m
        (Ir.MemBlock.addr blk + ofs :: Ir.MemBlock.addr blk + ofs + sz :: nil))
        as blks'.
      assert (List.In (bid, blk) blks').
      { apply Ir.Memory.inbounds_blocks2_In with (m := m)
          (abs_ofs1 := Ir.MemBlock.addr blk + ofs)
          (abs_ofs2 := Ir.MemBlock.addr blk + ofs + sz).
        - congruence.
        - assumption.
        - congruence.
        - congruence.
        - congruence.
        - apply PeanoNat.Nat.lt_neq.
          apply PeanoNat.Nat.lt_add_pos_r.
          assumption.
      }
      assert (List.length blks' < 2).
      { eapply Ir.Memory.inbounds_blocks2_singleton with
            (ofs1 := Ir.MemBlock.addr blk + ofs)
            (ofs2 := Ir.MemBlock.addr blk + ofs + sz).
        eassumption.
        apply PeanoNat.Nat.lt_neq.
        apply PeanoNat.Nat.lt_add_pos_r.
        assumption.
        congruence.
      }
      destruct blks' as [| blk1' blks'].
      * inversion H.
      * destruct blks'.
        simpl.
        simpl in H.
        destruct H as [H | H].
        -- rewrite H. simpl.
           rewrite Minus.minus_plus.
           reflexivity.
        -- inversion H.
        -- simpl in H1.
           assert (2 + length blks' >= 2).
           { apply PeanoNat.Nat.le_add_r. }
           replace (S (S (length blks'))) with (2 + length blks') in H2.
           apply Lt.le_not_lt in H2.
           omega.
           reflexivity.
      * omega.
      * omega.
    + inversion HP'.
  }
  { unfold ptr_to_phy in HP'.
    inv HP'.
    remember (get_deref m (Ir.pphy o [] None) sz) as blks.
    dup Heqblks.
    symmetry in Heqblks0.
    apply get_deref_singleton in Heqblks0; try assumption.
    destruct Heqblks0.
    { destruct H. destruct H. inv H.
      destruct x. destruct p. simpl in H0.
      apply get_deref_phy_I with (I := Is) in H1; try congruence; try omega.
      destruct H1.
      { apply get_deref_phy_cid with (cid := cid) in H; try congruence; try omega.
        destruct H; try congruence. }
      { eapply get_deref_phy_cid2 with (cid := cid) in H; try congruence; try omega. }
    }
    { rewrite H in Heqblks.
      symmetry in Heqblks.
      eapply get_deref_phy_I2 with (I := Is) in Heqblks; try eauto.
      eapply get_deref_phy_cid2 with (cid := cid) in Heqblks; try eauto.
      congruence.
    }
  } 
Qed.

(**************************************************
 Lemmas about load_bytes & store_bytes & store_val
 **************************************************)

(* Theorem:
   storing loaded bytes into the same location doesn't
   change memory. *)
Theorem load_store_bytes:
  forall (m:Ir.Memory.t) (wf:Ir.Memory.wf m) (sz:nat)
         (p:Ir.ptrval)
         (HSZ:sz > 0)
         (HDEREF:deref m p sz = true),
    store_bytes m p (load_bytes m p sz) = m.
Proof.
  intros.
  unfold load_bytes.
  unfold store_bytes.
  unfold deref in HDEREF.
  remember (get_deref m p sz) as bos.
  destruct bos as [| [[bid mb] ofs] bos'].
  { inversion HDEREF. }
  symmetry in Heqbos.
  assert (HRES := get_deref_singleton m wf p sz ((bid, mb, ofs)::bos')
                                      HSZ Heqbos).
  destruct HRES.
  - destruct H as [bo' [H1 H2]].
    inversion H1.
    rewrite H3 in *.
    rewrite <- H0 in *. clear H0 H3.
    simpl in H2.
    assert (HINV:Ir.MemBlock.alive mb &&
            Ir.MemBlock.inbounds ofs mb &&
            Ir.MemBlock.inbounds (ofs+sz) mb = true).
    { apply get_deref_inv with (m := m) (bid := bid) (p := p).
      assumption. assumption. assumption. assumption. }
    repeat (rewrite andb_true_iff in HINV).
    destruct HINV as [[HA HB] HC].
    unfold Ir.MemBlock.inbounds in *.

    rewrite Ir.MemBlock.bytes_length.
    rewrite Heqbos.
    rewrite Ir.MemBlock.set_bytes_self.
    { rewrite Nat.leb_le in HC.
      rewrite Nat.le_ngt in HC.
      rewrite <- Nat.ltb_nlt in HC.
      rewrite HC.
      apply Ir.Memory.set_get_id. assumption. assumption.
    }
    rewrite Ir.MemBlock.wf_clen.
    apply leb_complete. assumption.
    apply Ir.Memory.wf_blocks with (m := m) (i := bid).
    assumption. apply Ir.Memory.get_In with (m := m). congruence.
    reflexivity.
    rewrite Ir.MemBlock.wf_clen.
    apply leb_complete. assumption.
    apply Ir.Memory.wf_blocks with (m := m) (i := bid).
    assumption. apply Ir.Memory.get_In with (m := m). congruence.
    reflexivity.
  - inversion H.
Qed.

Lemma alive_P_ranges_set_bytes:
  forall m bid mb ofs bs
         (HWF:Ir.Memory.wf m)
         (HGET:Some mb = Ir.Memory.get m bid),
    Ir.Memory.alive_P_ranges (Ir.Memory.set m bid (Ir.MemBlock.set_bytes mb ofs bs)) =
    Ir.Memory.alive_P_ranges m.
Proof.
  intros.
  remember (Ir.Memory.set m bid (Ir.MemBlock.set_bytes mb ofs bs)) as m'.
  assert (HDECOMP: exists l1 l2 v0,
      Ir.Memory.blocks m = l1 ++ (bid, v0)::l2 /\
      Ir.Memory.blocks m' = l1 ++ (bid, Ir.MemBlock.set_bytes mb ofs bs)::l2 /\
      ~List.In bid (list_keys l1) /\
      ~List.In bid (list_keys l2)).
  { apply list_set_decompose.
    { inv HWF. assumption. }
    { eapply Ir.Memory.get_In with (blks := Ir.Memory.blocks m) in HGET.
      apply list_keys_In in HGET. assumption. reflexivity. }
    { unfold Ir.Memory.set in Heqm'.
      destruct m'. simpl in *.
      congruence. }
  }
  destruct HDECOMP as [l1 [l2 [v0 [HDECOMP1 [HDECOMP2 [HDECOMP3 HDECOMP4]]]]]].
  assert (HIN: List.In (bid, v0) (Ir.Memory.blocks m)).
  { rewrite HDECOMP1. apply List.in_or_app.
    right. constructor. reflexivity. }
  apply Ir.Memory.blocks_get with (m := m) in HIN.
  { simpl in HIN. rewrite HIN in HGET. inv HGET.
    unfold Ir.Memory.alive_P_ranges.
    unfold Ir.Memory.alive_blocks.
    rewrite HDECOMP1, HDECOMP2.
    rewrite filter_app.
    rewrite filter_app.
    rewrite map_app.
    rewrite map_app.
    rewrite concat_app.
    rewrite concat_app.
    simpl.
    assert (HALIVE:Ir.MemBlock.alive
                     (Ir.MemBlock.set_bytes v0 ofs bs) = Ir.MemBlock.alive v0).
    { unfold Ir.MemBlock.alive. unfold Ir.MemBlock.set_bytes.
      simpl. reflexivity. }
    rewrite HALIVE.
    des_if.
    { simpl.
      assert (HPR:Ir.MemBlock.P_ranges (Ir.MemBlock.set_bytes v0 ofs bs) =
                  Ir.MemBlock.P_ranges v0).
      { unfold Ir.MemBlock.P_ranges.
        unfold Ir.MemBlock.set_bytes.
        simpl. reflexivity. }
      rewrite HPR.
      reflexivity. }
    { reflexivity. }
  }
  assumption.
  reflexivity.
Qed.

Lemma set_bytes_wf:
  forall m bid mb ofs bs thety
         (HSZ:Ir.ty_bytesz thety > 0)
         (HWF:Ir.Memory.wf m)
         (HGET:Some mb = Ir.Memory.get m bid)
         (HLEN:Ir.ty_bytesz thety = List.length bs)
         (HOFS:ofs + List.length bs <= Ir.MemBlock.n mb),
    Ir.Memory.wf (Ir.Memory.set m bid
        (Ir.MemBlock.set_bytes mb ofs bs)).
Proof.
  intros.
  split. (* start to show wf of memory *)
  { intros.
    inv HWF.
    destruct (i =? bid) eqn:HBID.
    { rewrite PeanoNat.Nat.eqb_eq in HBID.
      subst i.
      apply Ir.Memory.get_In with (blks := Ir.Memory.blocks m) in HGET;
        try reflexivity.
      apply wf_blocks in HGET.
      unfold Ir.Memory.set in HAS.
      simpl in *.
      apply list_set_NoDup_In_unique in HAS.
      { rewrite HAS. unfold Ir.MemBlock.set_bytes.
        inv HGET.
        rewrite <- wf_clen in HOFS.
        split; try (simpl; assumption).
        simpl.
        repeat (rewrite app_length).
        rewrite skipn_length.
        rewrite firstn_length.
        rewrite Nat.min_l; try omega.
      }
      { assumption. }
    }
    { (* i != b *)
      rewrite PeanoNat.Nat.eqb_neq in HBID.
      apply wf_blocks with (i := i).
      unfold Ir.Memory.set in HAS.
      simpl in HAS.
      apply list_set_In_not_In in HAS; auto.
    }
  }
  { inv HWF.
    unfold Ir.Memory.set.
    simpl. eapply list_set_NoDup_key; eauto.
  }
  { inv HWF.
    unfold Ir.Memory.set. simpl.
    erewrite list_set_keys_eq; eauto.
  }
  { inv HWF.
    rewrite alive_P_ranges_set_bytes; try assumption.
    split; assumption.
  }
  { inv HWF.
    simpl.
    intros.
    destruct (i =? bid) eqn:HBID.
    { rewrite PeanoNat.Nat.eqb_eq in HBID.
      subst i.
      apply list_set_NoDup_In_unique in HAS; try assumption.
      rewrite HAS. unfold Ir.MemBlock.set_bytes.
      simpl. eapply wf_blocktime.
      eapply Ir.Memory.get_In in HGET. eapply HGET.
      reflexivity.
    }
    { rewrite PeanoNat.Nat.eqb_neq in HBID.
      apply list_set_In_not_In in HAS.
      { eapply wf_blocktime. eassumption. }
      { eassumption. }
    }
  }
Qed.

(* Theorem:
   store_val preservees wellformedness of memory. *)
Theorem store_val_wf:
  forall m (HWF:Ir.Memory.wf m) p v t
      (HSZ:Ir.ty_bytesz t > 0)
      (HDEREF:deref m p (Ir.ty_bytesz t) = true),
    Ir.Memory.wf (store_val m p v t).
Proof.
  intros.
  unfold deref in HDEREF.
  des_ifs.
  unfold store_val.
  unfold store_bytes.
  destruct t as [isz | pty].
  { destruct v; try assumption.
    des_ifs.
    eapply set_bytes_wf; try eassumption.
    { apply get_deref_singleton in Heq1.
      destruct Heq1.
      { destruct H. destruct H. inv H. simpl in H0. congruence. }
      { inv H. }
      { assumption. }
      { rewrite PeanoNat.Nat.eqb_eq in Heq0.
        omega. }
    }
    { rewrite PeanoNat.Nat.eqb_eq in Heq0.
      assumption. }
    { rewrite Nat.ltb_ge in Heq2.
      assumption. }
  }
  { destruct v; try assumption.
    des_ifs.
    eapply set_bytes_wf; try eassumption.
    { apply get_deref_singleton in Heq1.
      destruct Heq1.
      { destruct H. destruct H. inv H. simpl in H0. congruence. }
      { inv H. }
      { assumption. }
      { rewrite PeanoNat.Nat.eqb_eq in Heq0.
        omega. }
    }
    { rewrite PeanoNat.Nat.eqb_eq in Heq0.
      assumption. }
    { rewrite Nat.ltb_ge in Heq2.
      assumption. }
  }
Qed.

Lemma fresh_bid_store_val:
  forall m p v t,
    Ir.Memory.fresh_bid (Ir.store_val m p v t) =
    Ir.Memory.fresh_bid m.
Proof.
  intros.
  unfold Ir.store_val. unfold Ir.store_bytes.
  unfold Ir.Memory.set.
  des_ifs.
Qed.


End Ir.
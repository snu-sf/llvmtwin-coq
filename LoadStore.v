Require Import Lang.
Require Import Memory.
Require Import State.
Require Import Bool.
Require Import List.
Require Import BinNatDef.
Require Import Omega.

Module Ir.


Definition get_deref_blks_phyptr (m:Ir.Memory.t) (o:nat) (Is:list nat)
           (cid:option Ir.callid) (sz:nat)
: list (Ir.blockid * Ir.MemBlock.t) :=
  match (Ir.Memory.inbounds_blocks_all m (o::(o+sz)::Is)) with
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
  | Ir.plog (bid, ofs) => (* Logical pointer *)
    match (Ir.Memory.get m bid) with
    | None => nil (* No such block *)
    | Some blk =>
      if Ir.MemBlock.alive blk && Ir.MemBlock.inbounds ofs blk &&
         Ir.MemBlock.inbounds (ofs + sz) blk then
        (bid, blk, ofs)::nil
      else nil
    end
  | Ir.pphy (o, Is, cid) => (* Physical pointer *)
    List.map (fun mb => (mb.(fst), mb.(snd), o - Ir.MemBlock.addr mb.(snd)))
             (get_deref_blks_phyptr m o Is cid sz)
  end.

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

Definition load_val (m:Ir.Memory.t) (p:Ir.ptrval) (t:Ir.ty): Ir.val :=
  let bytes := load_bytes m p (Nat.div (7 + Ir.ty_bitsz t) 8) in
  match t with
  | Ir.ity bitsz =>
    match Ir.Byte.getint bytes bitsz with
    | None => Ir.poison
    | Some n => Ir.num (N.modulo n (N.shiftl 1 (N.of_nat bitsz)))
    end
  | Ir.ptrty _ =>
    match Ir.Byte.getptr bytes with
    | None => Ir.poison
    | Some p => Ir.ptr p
    end
  end.

Definition store_bytes (m:Ir.Memory.t) (p:Ir.ptrval) (bs:list Ir.Byte.t)
:Ir.Memory.t :=
  match get_deref m p (List.length bs) with
  | nil => m
  | (bid, blk, ofs)::_ =>
    Ir.Memory.set m bid (Ir.MemBlock.set_bytes blk ofs bs)
  end.

Definition store_val (m:Ir.Memory.t) (p:Ir.ptrval) (v:Ir.val) (t:Ir.ty)
: Ir.Memory.t :=
  match (t, v) with
  | (Ir.ity bitsz, Ir.num n) =>
    store_bytes m p (Ir.Byte.ofint n bitsz)
  | (Ir.ptrty pty, Ir.ptr pv) =>
    store_bytes m p (Ir.Byte.ofptr pv)
  | _ => m
  end.

(***********************************************
                Lemmas about get_deref
 ***********************************************)

(* Theorem: get_deref log(bid, ofs) either returns the input (bid, block, ofs)
   or returns nothing. *)
Theorem get_deref_log:
  forall (m:Ir.Memory.t) bid ofs sz bos blk
         (HDEREF: get_deref m (Ir.plog (bid, ofs)) sz = bos)
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
         (HDEREF: exists e, get_deref m (Ir.plog (bid, ofs)) sz = e::nil)
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

(* Lemma: get_deref_blks_byaddrs returns at most one alive block,
   if offsets have two disjoint numbers *)
Lemma get_deref_blks_phyptr_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) o Is cid sz bos
         (HSZ: 0 < sz)
         (HDEREF: get_deref_blks_phyptr m o Is cid sz = bos),
  (exists bo, bos = bo::nil /\ Ir.Memory.get m bo.(fst) = Some bo.(snd))
  \/ (bos = nil).
Proof.
  intros.
  unfold get_deref_blks_phyptr in HDEREF.
  remember (Ir.Memory.inbounds_blocks_all m (o::o+sz::Is)) as blks.
  assert (List.length blks < 2).
  {
    apply (Ir.Memory.inbounds_blocks_all_singleton2 m o (o+sz) blks Is).
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
          eapply Ir.Memory.inbounds_blocks_all_In2.
          eassumption.
        * right. congruence.
      + left. eexists. rewrite HDEREF.
        split. reflexivity.
        eapply Ir.Memory.blocks_get. assumption. reflexivity.
        eapply Ir.Memory.inbounds_blocks_all_In2. eassumption.
    - left. eexists. rewrite HDEREF.
      split. reflexivity. eapply Ir.Memory.blocks_get. assumption. reflexivity.
      eapply Ir.Memory.inbounds_blocks_all_In2. eassumption.
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

(* Theorem: get_deref always returns at most one block. *)
Theorem get_deref_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) (p:Ir.ptrval) (sz:nat) bos
         (HSZ: 0 < sz)
         (HDEREF: get_deref m p sz = bos),
  (exists bo, bos = bo::nil /\ Ir.Memory.get m bo.(fst).(fst) = Some bo.(fst).(snd))
  \/ (bos = nil).
Proof.
  intros.
  destruct p.
  - (* logical ptr *)
    destruct p as [bid ofs].
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
    destruct p as (p', cid).
    destruct p' as (o, Is).
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


(* Convert a logical pointer to physical pointer. *)
Definition log_to_phy (m:Ir.Memory.t) (bid:Ir.blockid) (ofs:nat): option Ir.ptrval :=
  match Ir.Memory.get m bid with
  | None => None
  | Some bb => Some (Ir.pphy (Ir.MemBlock.addr bb + ofs, nil, None))
  end.

(* Convert a pointer to physical pointer. *)
Definition ptr_to_phy (m:Ir.Memory.t) (p:Ir.ptrval): option Ir.ptrval :=
  match p with
  | Ir.plog (bid, ofs) => log_to_phy m bid ofs
  | Ir.pphy (o, Is, cid) => Some (Ir.pphy (o, nil, None))
  end.


(* Theorem: A logical pointer (bid, ofs) and a
   physical pointer which is converted from (bid, ofs) both
   access a same memory block with same offset, if
   access size is larger than zero. *)
Theorem get_deref_log_phy_same:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) bid ofs p' (sz:nat) bo
         (HSZ: 0 < sz)
         (HDEREF: get_deref m (Ir.plog (bid, ofs)) sz = bo::nil)
         (HP':log_to_phy m bid ofs  = Some p'),
    get_deref m p' sz = bo::nil.
Proof.
  intros.
    unfold log_to_phy in HP'.
  remember (Ir.Memory.get m bid) as blk.
  symmetry in Heqblk.
  destruct blk as [blk | ].
  + remember (Ir.MemBlock.alive blk) as alive.
    remember (Ir.MemBlock.inbounds ofs blk) as inb1.
    remember (Ir.MemBlock.inbounds (ofs + sz) blk) as inb2.
    inversion HP'.
    assert (HLOG := get_deref_log m bid ofs sz (bo::nil) blk HDEREF Heqblk).
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
    destruct HLOG.
    rewrite H.
    unfold get_deref.
    unfold get_deref_blks_phyptr.
    remember (Ir.Memory.inbounds_blocks_all m
             (Ir.MemBlock.addr blk + ofs :: Ir.MemBlock.addr blk + ofs + sz :: nil))
               as blks'.
    assert (List.In (bid, blk) blks').
    { apply Ir.Memory.inbounds_blocks_all_In with (m := m)
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
    { eapply Ir.Memory.inbounds_blocks_all_singleton with
          (ofs1 := Ir.MemBlock.addr blk + ofs)
          (ofs2 := Ir.MemBlock.addr blk + ofs + sz).
      eassumption.
      apply PeanoNat.Nat.lt_neq.
      apply PeanoNat.Nat.lt_add_pos_r.
      assumption.
      congruence.
    }
    destruct blks' as [| blk1' blks'].
    * inversion H1.
    * destruct blks'.
      simpl.
      simpl in H1.
      destruct H1.
      -- rewrite H1. simpl.
         rewrite Minus.minus_plus.
         reflexivity.
      -- inversion H1.
      -- simpl in H2.
         assert (2 + length blks' >= 2).
         { apply PeanoNat.Nat.le_add_r. }
         replace (S (S (length blks'))) with (2 + length blks') in H2.
         apply Lt.le_not_lt in H3.
         apply H3 in H2. inversion H2.
         reflexivity.
    * inversion H.
    * rewrite PeanoNat.Nat.add_comm with (n := Ir.MemBlock.addr blk) (m := ofs).
      rewrite PeanoNat.Nat.add_shuffle0.
      reflexivity.
    * rewrite PeanoNat.Nat.add_comm.
      reflexivity.
  + inversion HP'.
Qed.

(* This is for a physical pointer. WIP
  - destruct p as [p cid].
    destruct p as [o Is].
    simpl in HP'.
    inversion HP'.
    unfold get_deref in HDEREF.
    unfold get_deref_blks_phyptr in HDEREF.
    remember (Ir.Memory.inbounds_blocks_all m (o::o+sz::Is)) as res.
    assert (List.length res < 2).
    { eapply Ir.Memory.inbounds_blocks_all_singleton2 with
          (ofs1 := o) (ofs2 := o+sz).
      eassumption.
      apply PeanoNat.Nat.lt_neq.
      apply PeanoNat.Nat.lt_add_pos_r.
      assumption.
      rewrite <- Heqres. reflexivity.
    }
    destruct res as [| bo1 res].
    + simpl in HDEREF. inversion HDEREF.
    + destruct res.
      destruct bo1 as [bid1 blk1].
      symmetry in Heqres.
      assert (HCOND := Ir.Memory.inbounds_blocks_all_forallb2 m
                        (o::o+sz::Is) ((bid1,blk1)::nil) Heqres).
      simpl in HCOND.
      repeat (rewrite andb_true_r in HCOND).
      repeat (rewrite andb_true_iff in HCOND).
      destruct HCOND as [HCOND1 HCOND].
      destruct HCOND as [HCOND2 HCOND].
      destruct cid as [ | cid].
      * remember (Ir.Memory.calltime m c) as calltime.
        destruct calltime.
        simpl in HDEREF.
        remember (Ir.MemBlock.alive_before t blk1) as ab.
        destruct ab.
        -- simpl in HDEREF.
           unfold get_deref.
           unfold get_deref_blks_phyptr.
           remember (Ir.Memory.inbounds_blocks_all m (o::o+sz::nil)) as res'.
           assert (List.In (bid1, blk1) res').
           {
             eapply Ir.Memory.inbounds_blocks_all_In.
             - e
           }
*)

(***********************************************
      Lemmas about load_bytes & store_bytes
 ***********************************************)

Theorem load_store_bytes:
  forall (m:Ir.Memory.t) (wf:Ir.Memory.wf m) (sz:nat)
         (p:Ir.ptrval)
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
  assert (Ir.Memory.get m bid = Some mb).
  { unfold get_deref in Heqbos.
    remember (Ir.Memory.get m bid) as blk.
    destruct p as [[bid' ofs'] | [[o Is] cid]].
    - remember (Ir.Memory.get m bid') as blk'.
      destruct blk'.
      + destruct (Ir.MemBlock.alive t && Ir.MemBlock.inbounds ofs' t &&
             Ir.MemBlock.inbounds (ofs' + sz) t).
        * inversion Heqbos.
          congruence.
        * inversion Heqbos.
      + inversion Heqbos.
    - unfold get_deref_blks_phyptr in Heqbos.
      destruct cid.
      destruct (Ir.Memory.calltime m c).
    
  rewrite bytes_length.
  rewrite <- Heqbos.
  rewrite set_bytes_self.

End Ir.
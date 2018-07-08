Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Memory.
Require Import Bool.
Require Import List.
Require Import BinNatDef.
Require Import Omega.

Module Ir.


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
  let bytes := load_bytes m p (Ir.ty_bytesz t) in
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

(* Theorem: get_deref log(bid, ofs) either returns the input (bid, block, ofs)
   or returns nothing. *)
Theorem get_deref_log:
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


Theorem get_deref_ofs_lt_MEMSZ:
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
    assert (Ir.MemBlock.addr mb + Ir.MemBlock.n mb <= Ir.MEMSZ).
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
Theorem get_deref_log_phy_same:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) bid ofs p' (sz:nat) bo
         (HSZ: 0 < sz)
         (HDEREF: get_deref m (Ir.plog bid ofs) sz = bo::nil)
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
    { eapply Ir.Memory.inbounds_blocks2_singleton2 with
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
      assert (HCOND := Ir.Memory.inbounds_blocks2_forallb2 m
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
           remember (Ir.Memory.inbounds_blocks2 m (o::o+sz::nil)) as res'.
           assert (List.In (bid1, blk1) res').
           {
             eapply Ir.Memory.inbounds_blocks_In.
             - e
           }
*)

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
    apply Ir.Memory.set_get_id. assumption. assumption.

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

(* Theorem:
   storing loaded bytes into the same location doesn't
   change memory. *)
Theorem store_val_wf:
  forall m m' (HWF:Ir.Memory.wf m) p v t
      (HSTORE:m' = store_val m p v t)
      (HDEREF:deref m p (Ir.ty_bytesz t) = true),
    Ir.Memory.wf m'.
Admitted.

End Ir.
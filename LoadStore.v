Require Import Memory.
Require Import Bool.
Require Import List.

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

(* Lemma: get_deref_blks_byaddrs returns at most one alive block,
   if offsets have two disjoint numbers *)
Lemma get_deref_blks_phyptr_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) o Is cid sz bos
         (HSZ: 0 < sz)
         (HDEREF: get_deref_blks_phyptr m o Is cid sz = bos),
  (exists bo, bos = bo::nil) \/ (bos = nil).
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
        * left. eexists. rewrite HDEREF. reflexivity.
        * right. congruence.
      + left. eexists. rewrite HDEREF. reflexivity.
    - left. eexists. rewrite HDEREF. reflexivity.
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
  (exists bo, bos = bo::nil) \/ (bos = nil).
Proof.
  intros.
  destruct p.
  - (* logical ptr *)
    destruct p as [bid ofs].
    unfold get_deref in HDEREF.
    destruct (Ir.Memory.get m bid).
    remember (Ir.MemBlock.alive t && Ir.MemBlock.inbounds ofs t &&
              Ir.MemBlock.inbounds (ofs + sz) t) as cond in HDEREF.
    destruct cond; rewrite <- HDEREF.
    + left. eexists. reflexivity.
    + right. reflexivity.
    + right. congruence.
  - unfold get_deref in HDEREF.
    destruct p as (p', cid).
    destruct p' as (o, Is).
    remember (get_deref_blks_phyptr m o Is cid sz) as blks.
    assert ((exists bo0, blks = bo0::nil) \/ (blks = nil)).
    { eapply get_deref_blks_phyptr_singleton.
      eassumption.
      eassumption.
      rewrite <- Heqblks. reflexivity. }
    destruct H.
    { destruct H.
      rewrite H in HDEREF.
      simpl in HDEREF.
      left. eexists. rewrite <- HDEREF.
      reflexivity.
    }
    right. rewrite H in HDEREF. simpl in HDEREF. congruence.
Qed.


End Ir.
Require Import Memory.
Require Import Bool.
Require Import List.

Module Ir.


(* get_deref_blks_byaddrs returns all alive blocks which have
   ofss as their inbounds. *)
Definition get_deref_blks_byaddrs (m:Ir.Memory.t) (ofss:list nat)
: list (Ir.blockid * Ir.MemBlock.t) :=
  List.fold_left
           (fun blks (ofs:nat) =>
              List.filter (fun b => Ir.MemBlock.inbounds_abs ofs b.(snd)) blks)
           ofss
           m.(Ir.Memory.blocks).

Definition get_deref_blks_phyptr (m:Ir.Memory.t) (o:nat) (Is:list nat)
           (cid:option Ir.callid) (sz:nat)
: list (Ir.blockid * Ir.MemBlock.t) :=
  match (get_deref_blks_byaddrs m (o::(o+sz)::Is)) with
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

(* get_deref returns (block, offset) list which will be dereferenced
   from pointer p and access size sz.
   We'll show that the list of (block, offset) is a singleton later. *)
Definition get_deref (m:Ir.Memory.t) (p:Ir.ptrval) (sz:nat)
: list (Ir.MemBlock.t * nat) :=
  match p with
  | Ir.plog (bid, ofs) => (* Logical pointer *)
    match (Ir.Memory.get m bid) with
    | None => nil (* No such block *)
    | Some blk =>
      if Ir.MemBlock.alive blk && Ir.MemBlock.inbounds blk ofs &&
         Ir.MemBlock.inbounds blk (ofs + sz) then
        (blk, ofs)::nil
      else nil
    end
  | Ir.pphy (o, Is, cid) => (* Physical pointer *)
    List.map (fun mb => (mb, o - Ir.MemBlock.addr mb))
             (get_deref_blks_phyptr m o Is cid sz)
  end.

Definition deref (m:Ir.Memory.t) (p:Ir.ptrval) (sz:nat): bool :=
  match (get_deref m p sz) with
  | nil => false | _=> true
  end.

(* Lemma: get_deref_blks_byaddrs returns at most one alive block,
   if offsets have two disjoint numbers *)
Lemma get_deref_blks_byaddrs_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) ( cid (sz:nat)
         (bos:list Ir.MemBlock.t)
         (HSZ: 0 < sz)
         (HDEREF: get_deref_blks_phyptr m o Is cid sz = bos),
  (exists bo, bos = bo::nil) \/ (bos = nil).
Proof.
  intros.
  unfold get_deref_blks_phyptr in HDEREF.
  remember (Ir.Memory.inbounds_blocks m o) as blks.
  assert (List.length blks < 3).
  {
    apply (Ir.Memory.inbounds_blocks_atmost_2 m o).
    assumption. congruence.
  }
  destruct blks as [| b1 blks].
  { right. simpl in HDEREF. congruence. }
  destruct cid as [cid |].
  - destruct (Ir.Memory.calltime m cid) as [cid' |] eqn:HCT.
    
Qed.

Lemma get_deref_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) (p:Ir.ptrval) (sz:nat)
         (bos:list (Ir.MemBlock.t * nat))
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
    remember (Ir.MemBlock.alive t && Ir.MemBlock.inbounds t ofs &&
              Ir.MemBlock.inbounds t (ofs + sz)) as cond in HDEREF.
    destruct cond; rewrite <- HDEREF.
    + left. eexists. reflexivity.
    + right. reflexivity.
    + right. congruence.
  - unfold get_deref in HDEREF.
    
Qed.


End Ir.
Require Import Memory.
Require Import Bool.
Require Import List.

Module Ir.

(* get_deref returns (block, offset) list which will be dereferenced
   from pointer p and access size sz.
   We'll show that the list of (block, offset) is a singleton later. *)

Definition get_deref_blks_phyptr (m:Ir.Memory.t) (o:nat) (Is:list nat)
           (cid:option Ir.callid) (sz:nat)
: list Ir.MemBlock.t :=
  List.map snd
  (match Ir.Memory.inbounds_blocks m o with
  | nil => nil (* No such block *)
  | blks =>
    match cid with
    | None => blks (* No cid constraint *)
    | Some c =>
      match Ir.Memory.calltime m c with
      | None => blks (* The function is finished. *)
      | Some t => List.filter
         (fun mb => Nat.ltb t mb.(snd).(Ir.MemBlock.r).(fst)) blks
      end
    end
  end).

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

Lemma get_deref_blks_phyptr_singleton:
  forall (m:Ir.Memory.t) (m_wf:Ir.Memory.wf m) (o:nat) (Is:list nat) cid (sz:nat)
         (bos:list Ir.MemBlock.t)
         (HSZ: 0 < sz)
         (HDEREF: get_deref_blks_phyptr m o Is cid sz = bos),
  (exists bo, bos = bo::nil) \/ (bos = nil).
Proof.
  intros.
  unfold get_deref_blks_phyptr in HDEREF.
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
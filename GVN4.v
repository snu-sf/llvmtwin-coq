Require Import Bool.
Require Import Sorting.Permutation.
Require Import Omega.
Require Import sflib.
Require Import Lia.

Require Import Common.
Require Import Value.
Require Import Lang.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import SmallStepAux.
Require Import SmallStepWf.
Require Import Refinement.
Require Import SmallStepRefinement.
Require Import Reordering.
Require Import GVN1.

Module Ir.

Module GVN4.

(**************************************************************
  This file proves validity of the fourth GVN optimization case:
 4. Either p or q is computed by a series of gep inbounds with
     positive offsets, based on the same base pointer.

  High-level structure of proof is as follows:
  (1) We define the notion of `gepinbs p q`, meaning
      that p and q have same base pointer p0, and have gep inbounds
      with positive offsets.
  (2) We show that if p0 is a logical pointer, p and q are the same.
  (3) We show that if p0 is a physical pointer,
      after calculation, given p=Phy(o1, I1, cid1) and
      q=Phy(o2, I2, cid2), min(I1) = min(I2) /\ max(I2) = max(I2)
      /\ o1 = o2 /\ cid1 = cid2. This relation is defined as
      `phy_Isamerange p q`.
  (4) We show that if `phy_minmaxI p q` holds, then all instructions
      behave identically.
 **************************************************************)

Inductive gepinbs: Ir.Memory.t -> Ir.val -> Ir.val -> Prop :=
| gi_base: forall m p, gepinbs m p p
| gi_gep:
    forall m p q ofs p' q' t
           (HBASE:gepinbs m (Ir.ptr p) (Ir.ptr q))
           (HGEP1:p' = Ir.SmallStep.gep p ofs t m true)
           (HGEP2:q' = Ir.SmallStep.gep q ofs t m true)
           (HPOS:ofs * Ir.ty_bytesz t < (Nat.shiftl 1 (Ir.SmallStep.OPAQUED_PTRSZ - 1))),
      gepinbs m p' q'.

Definition list_max (n:nat) (l:list nat): Prop :=
  List.In n l /\ List.Forall (fun m => m <= n) l.

Definition list_min (n:nat) (l:list nat): Prop :=
  List.In n l /\ List.Forall (fun m => m >= n) l.

Lemma Forall_and {X:Type}:
  forall (l:list X) (f g:X -> Prop)
         (HF:List.Forall f l)
         (HG:List.Forall g l),
    List.Forall (fun x => f x /\ g x) l.
Proof.
  intros.
  induction l.
  { constructor. }
  { inv HF. inv HG.
    constructor. split; ss. eapply IHl; eauto.
  }
Qed.

Lemma list_minmax:
  forall (l:list nat) n m
         (HMIN:list_min n l)
         (HMAX:list_max m l),
    List.Forall (fun x => n <= x <= m) l.
Proof.
  intros.
  eapply Forall_and.
  eapply HMIN.
  eapply HMAX.
Qed.

Lemma lsubseq_split_len2 {X:Type}:
  forall (l:list X) (x1 x2:X)
         (HLSS:lsubseq l (x1::x2::nil)),
    exists l1 l2 l3,
      l = l1 ++ x1 :: l2 ++ x2 :: l3.
Proof.
  intros.
  induction l.
  { inv HLSS. }
  { inv HLSS.
    { eapply lsubseq_In in H0.
      2: constructor; ss.
      eapply List.in_split in H0.
      inv H0. inv H.
      exists [].
      exists x.
      exists x0.
      simpl. ss.
    }
    { apply IHl in H2.
      inv H2. inv H. inv H0.
      exists (a::x).
      eexists.
      eexists.
      simpl. ss.
    }
  }
Qed.

Lemma inbounds_abs_minmax:
  forall ofsmin ofsmax mb ofss
         (HMIN:list_min ofsmin ofss)
         (HMAX:list_max ofsmax ofss)
         (HINB:Ir.MemBlock.inbounds_abs ofsmin mb = true)
         (HINB:Ir.MemBlock.inbounds_abs ofsmax mb = true),
    List.forallb (fun i : nat => Ir.MemBlock.inbounds_abs i mb)
                 ofss = true.
Proof.
  intros.
  unfold Ir.MemBlock.inbounds_abs in *.
  unfold in_range in *.
  rewrite List.forallb_forall.
  intros.
  repeat (rewrite andb_true_iff in *). repeat (rewrite Nat.leb_le in *).
  unfold list_min in HMIN.
  unfold list_max in HMAX.
  inv HMIN. inv HMAX.
  SearchAbout List.Forall.
  rewrite List.Forall_forall in *.
  dup H.
  apply H1 in H4. apply H3 in H. omega.
Qed.

Lemma list_min_cons:
  forall x l y
         (HMIN:list_min x l)
         (HLE:x <= y),
    list_min x (y::l).
Proof.
  intros.
  unfold list_min in *.
  inv HMIN.
  split. right. eauto.
  rewrite List.Forall_forall in *. intros.
  destruct H1. omega. apply H0. ss.
Qed.

Lemma list_max_cons:
  forall x l y
         (HMAX:list_max x l)
         (HLE:x >= y),
    list_max x (y::l).
Proof.
  intros.
  unfold list_max in *.
  inv HMAX.
  split. right. eauto.
  rewrite List.Forall_forall in *. intros.
  destruct H1. omega. apply H0. ss.
Qed.

Lemma list_minmax_le:
  forall x l y
         (HMIN:list_min x l)
         (HMAX:list_max y l),
    x <= y.
Proof.
  intros.
  unfold list_max in *.
  unfold list_min in *.
  rewrite List.Forall_forall in *.
  inv HMIN. inv HMAX.
  apply H0 in H1. omega.
Qed.

Lemma list_min_Permutation:
  forall x l  l'
         (HMIN:list_min x l)
         (HPERM:Permutation l l'),
    list_min x l'.
Proof.
  intros.
  unfold list_min in *.
  inv HMIN.
  exploit Permutation_in. eassumption. eassumption. intros.
  split. ss.
  rewrite List.Forall_forall in *.
  intros. eapply H0. 
  eapply Permutation_in. eapply Permutation_sym in HPERM. eassumption.
  ss.
Qed.

Lemma list_max_Permutation:
  forall x l  l'
         (HMAX:list_max x l)
         (HPERM:Permutation l l'),
    list_max x l'.
Proof.
  intros.
  unfold list_max in *.
  inv HMAX.
  exploit Permutation_in. eassumption. eassumption. intros.
  split. ss.
  rewrite List.Forall_forall in *.
  intros. eapply H0. 
  eapply Permutation_in. eapply Permutation_sym in HPERM. eassumption.
  ss.
Qed.

Lemma inbounds_blocks2_minmax:
  forall m ofss ofsmin ofsmax
         (HWF:Ir.Memory.wf m)
         (HMIN:list_min ofsmin ofss)
         (HMAX:list_max ofsmax ofss)
         (HDIFF:ofsmin <> ofsmax),
    Ir.Memory.inbounds_blocks2 m ofss =
    Ir.Memory.inbounds_blocks2 m (ofsmin::ofsmax::nil).
Proof.
  intros.
  assert (lsubseq ofss (ofsmin::ofsmax::nil) \/
          lsubseq ofss (ofsmax::ofsmin::nil)).
  { unfold list_min in HMIN.
    unfold list_max in HMAX.
    inv HMIN. inv HMAX.
    exploit (@In_split2 nat).
    eassumption. eassumption. eassumption.
    intros HH. inv HH. inv H3. inv H4.
    inv H3.
    { left. eapply lsubseq_append2. constructor.
      eapply lsubseq_append2. constructor. constructor.
    }
    { right. eapply lsubseq_append2. constructor.
      eapply lsubseq_append2. constructor. constructor.
    }
  }
  remember (Ir.Memory.inbounds_blocks2 m ofss) as blks1.
  remember (Ir.Memory.inbounds_blocks2 m [ofsmin; ofsmax]) as blks2.
  symmetry in Heqblks1.
  symmetry in Heqblks2.
  dup Heqblks2.
  eapply Ir.Memory.inbounds_blocks2_singleton2 in Heqblks2.
  destruct H.
  { dup Heqblks0.
    eapply Ir.Memory.inbounds_blocks2_lsubseq2 in Heqblks0.
    2: eapply Heqblks1.
    destruct blks2.
    { destruct blks1. ss. inv Heqblks0. }
    destruct blks2.
    { assert (HPERM:exists ofss', Permutation (ofsmin::ofsmax::ofss') ofss ).
      { apply lsubseq_split_len2 in H.
        inv H. inv H0. inv H.
        exists (x ++ x0 ++ x1).
        replace (ofsmax::x++x0++x1) with ((ofsmax::x)++(x0++x1)) by ss.
        eapply perm_trans with (l' := (ofsmax::x) ++ ofsmin:: x0 ++ x1).
        eapply Permutation_middle.
        simpl.
        replace (x++ofsmin::x0++x1) with ((x++ofsmin::x0)++x1).
        replace (x++ofsmin::x0++ofsmax::x1) with
                ((x++ofsmin::x0)++ofsmax::x1).
        eapply Permutation_middle.
        rewrite <- List.app_assoc. ss.
        rewrite <- List.app_assoc. ss.
      }
      destruct HPERM as [ofss' HPERM].

      assert (HEQ:Ir.Memory.inbounds_blocks2 m ofss =
                  Ir.Memory.inbounds_blocks2 m (ofsmin::ofsmax::ofss')).
      { eapply Ir.Memory.inbounds_blocks2_Permutation. eapply HPERM. ss. }

      rewrite HEQ in Heqblks1.
      destruct p.
      assert (List.forallb (fun i : nat => Ir.MemBlock.inbounds_abs i t)
                           (ofsmin :: ofsmax :: ofss') = true).
      { eapply inbounds_abs_minmax with (ofsmin := ofsmin) (ofsmax := ofsmax).
        { eapply list_min_Permutation.
          eassumption. apply Permutation_sym. eassumption.
        }
        { eapply list_max_Permutation.
          eassumption. apply Permutation_sym. eassumption.
        }
        { eapply Ir.Memory.inbounds_blocks2_forallb in Heqblks3.
          simpl in Heqblks3. rewrite andb_true_r in Heqblks3. ss. }
        { eapply Ir.Memory.inbounds_blocks2_forallb2 in Heqblks3.
          simpl in Heqblks3. repeat (rewrite andb_true_r in Heqblks3).
          rewrite andb_true_iff in Heqblks3. inv Heqblks3. ss. }
      }
      eapply Ir.Memory.inbounds_blocks2_singleton4 with (m := m) (bid := b) in H0.
      rewrite Heqblks1 in H0.  ss.
      ss.
      { eapply Ir.Memory.In_get. ss.
        eapply Ir.Memory.inbounds_blocks2_In2.
        rewrite Heqblks3. ss.
      }
      { eapply Ir.Memory.inbounds_blocks2_alive in Heqblks3.
        simpl in Heqblks3. rewrite andb_true_r in Heqblks3. ss.
      }
      ss.
    }
    { simpl in Heqblks2. omega. }
    ss.
  }
  { assert (Ir.Memory.inbounds_blocks2 m [ofsmax; ofsmin] = blks2).
    { eapply Ir.Memory.inbounds_blocks2_Permutation with (I := [ofsmin; ofsmax]).
      eapply perm_swap. ss. }
    clear Heqblks0. rename H0 into Heqblks0.
    dup Heqblks0.
    eapply Ir.Memory.inbounds_blocks2_lsubseq2 in Heqblks0.
    2: eapply Heqblks1.
    destruct blks2.
    { destruct blks1. ss. inv Heqblks0. }
    destruct blks2.
    { assert (HPERM:exists ofss', Permutation (ofsmax::ofsmin::ofss') ofss ).
      { apply lsubseq_split_len2 in H.
        inv H. inv H0. inv H.
        exists (x ++ x0 ++ x1).
        replace (ofsmin::x++x0++x1) with ((ofsmin::x)++(x0++x1)) by ss.
        eapply perm_trans with (l' := (ofsmin::x) ++ ofsmax:: x0 ++ x1).
        eapply Permutation_middle.
        simpl.
        replace (x++ofsmax::x0++x1) with ((x++ofsmax::x0)++x1).
        replace (x++ofsmax::x0++ofsmin::x1) with
                ((x++ofsmax::x0)++ofsmin::x1).
        eapply Permutation_middle.
        rewrite <- List.app_assoc. ss.
        rewrite <- List.app_assoc. ss.
      }
      destruct HPERM as [ofss' HPERM].

      assert (HEQ:Ir.Memory.inbounds_blocks2 m ofss =
                  Ir.Memory.inbounds_blocks2 m (ofsmax::ofsmin::ofss')).
      { eapply Ir.Memory.inbounds_blocks2_Permutation. eapply HPERM. ss. }

      rewrite HEQ in Heqblks1.
      destruct p.
      assert (List.forallb (fun i : nat => Ir.MemBlock.inbounds_abs i t)
                           (ofsmax :: ofsmin :: ofss') = true).
      { eapply inbounds_abs_minmax with (ofsmin := ofsmin) (ofsmax := ofsmax).
        { eapply list_min_Permutation.
          eassumption. apply Permutation_sym.
          eassumption.
        }
        { eapply list_max_Permutation.
          eassumption. apply Permutation_sym. eassumption.
        }
        { eapply Ir.Memory.inbounds_blocks2_forallb2 in Heqblks3.
          simpl in Heqblks3. repeat (rewrite andb_true_r in Heqblks3).
          rewrite andb_true_iff in Heqblks3. inv Heqblks3. ss. }
        { eapply Ir.Memory.inbounds_blocks2_forallb in Heqblks3.
          simpl in Heqblks3. rewrite andb_true_r in Heqblks3. ss.
        }
      }
      eapply Ir.Memory.inbounds_blocks2_singleton4 with (m := m) (bid := b) in H0.
      rewrite Heqblks1 in H0.  ss.
      ss.
      { eapply Ir.Memory.In_get. ss.
        eapply Ir.Memory.inbounds_blocks2_In2.
        rewrite Heqblks3. ss.
      }
      { eapply Ir.Memory.inbounds_blocks2_alive in Heqblks3.
        simpl in Heqblks3. rewrite andb_true_r in Heqblks3. ss.
      }
      omega.
    }
    { simpl in Heqblks2. omega. }
    ss.
  }
  ss.
  ss.
Qed.

Definition phys_minmaxI (p q:Ir.ptrval): Prop :=
  exists o I1 I2 cid ofsmin ofsmax,
    (p = Ir.pphy o I1 cid /\ q = Ir.pphy o I2 cid /\
     list_min ofsmin I1 /\ list_min ofsmin I2 /\
     list_max ofsmax I1 /\ list_max ofsmax I2).

Lemma phys_minmaxI_get_deref:
  forall m p q sz
         (HWF:Ir.Memory.wf m)
         (HPMM:phys_minmaxI p q),
    Ir.get_deref m p sz = Ir.get_deref m q sz.
Proof.
  intros.
  unfold Ir.get_deref.
  inv HPMM.
  repeat (match goal with
  | [H:exists _, _ |- _] => destruct H
  | [H:_ /\ _ |- _] => destruct H
  end).
  rewrite H, H0.
  unfold Ir.get_deref_blks_phyptr.
  assert (Ir.Memory.inbounds_blocks2 m (x :: x + sz :: x0) =
          Ir.Memory.inbounds_blocks2 m [x3;x4]).
  { eapply inbounds_blocks2_minmax. ss. 
  inv HPMM. inv H. inv H0. inv H. inv H0. inv H. inv H0. inv H1.

End GVN4.

End Ir.
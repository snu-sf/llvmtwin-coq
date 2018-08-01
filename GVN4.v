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
Require Import Utf8.

Module Ir.

Module GVN4.

(**************************************************************
  This file proves validity of the fourth GVN optimization case:
 4. Either p or q is computed by a series of gep inbounds with
     positive offsets, based on the same base pointer.

  High-level structure of proof is as follows:
  (1) We define the notion of `gepinbs p q p0`, meaning
      that p and q have same base pointer p0, and have gep inbounds
      with positive offsets.
  (2) We show that if p0 is a logical pointer, p and q are the same.
  (3) We show that if p0 is a physical pointer,
      after calculation, given p=Phy(o1, I1, cid1) and
      q=Phy(o2, I2, cid2), min(I1) = min(I2) /\ max(I2) = max(I2)
      /\ o1 = o2 /\ cid1 = cid2. This relation is defined as
      `phys_minmaxI p q`.
      (2) and (3) are shown in `gepinbs_after_icmpeq_true`.
  (4) We show that if `phy_minmaxI p q` holds, then refinement
      holds for all instructions that has operand p replaced
      with q.
 **************************************************************)

Definition posofs (ofs:nat) (t:Ir.ty) :=
  ofs * Ir.ty_bytesz t < Nat.shiftl 1 (Ir.PTRSZ - 1).

Inductive gepinbs: Ir.Memory.t -> Ir.val -> Ir.val -> Ir.ptrval -> Prop :=
| gi_one: (* should have at least one GEP *)
    forall m p0 p q ofs1 ofs2 t1 t2
           (HGEP1:p = Ir.SmallStep.gep p0 ofs1 t1 m true)
           (HGEP2:q = Ir.SmallStep.gep p0 ofs2 t2 m true)
           (HPOS1:posofs ofs1 t1)
           (HPOS2:posofs ofs2 t2),
      gepinbs m p q p0
| gi_succ_l:
    forall m p q p0 ofs p' t
           (HBASE:gepinbs m (Ir.ptr p) (Ir.ptr q) p0)
           (HGEP1:p' = Ir.SmallStep.gep p ofs t m true)
           (HPOS:posofs ofs t),
      gepinbs m p' (Ir.ptr q) p0
| gi_succ_r:
    forall m p q p0 ofs q' t
           (HBASE:gepinbs m (Ir.ptr p) (Ir.ptr q) p0)
           (HGEP1:q' = Ir.SmallStep.gep q ofs t m true)
           (HPOS:posofs ofs t),
      gepinbs m (Ir.ptr p) q' p0.

Definition phys_minmaxI (p q:Ir.ptrval): Prop :=
  exists o I1 I2 cid ofsmin ofsmax,
    (p = Ir.pphy o I1 cid /\ q = Ir.pphy o I2 cid /\
     list_min ofsmin I1 /\ list_min ofsmin I2 /\
     list_max ofsmax I1 /\ list_max ofsmax I2).


(*********************************************************
 Important property of gepinbs:
  If gepinbs p q holds, and `icmp eq p, q` evaluates
    to true, then either p = q or phys_minmaxI holds.
 *********************************************************)

Lemma gepinbs_log_neverphy:
  forall m v1 l o v2 p0
         (HP1:Ir.ptr (Ir.plog l o) = v1)
         (HGEPINBS:gepinbs m v1 v2 p0),
    ~ exists o2 I2 cid2, v2 = Ir.ptr (Ir.pphy o2 I2 cid2).
Proof.
  intros.
  generalize dependent l.
  generalize dependent o.
  induction HGEPINBS.
  { intros. inv HP1. intros HH. inv HH. inv H0. inv H1.
    unfold Ir.SmallStep.gep in *.
    des_ifs.
  }
  { unfold Ir.SmallStep.gep in HGEP1.
    des_ifs. intros. inv HP1.
    intros HH. inv HH. inv H. inv H0. inv H.
    exploit IHHGEPINBS. ss. eexists. eexists. eexists. ss.
    eauto. }
  { intros. intros HH. inv HH. inv H. inv H0.
    unfold Ir.SmallStep.gep in H.
    des_ifs.
    exploit IHHGEPINBS. ss. do 3 eexists. ss. eauto.
    exploit IHHGEPINBS. ss. do 3 eexists. ss. eauto.
  }
Qed.

Lemma gepinbs_phy_neverlog:
  forall m v1 o I cid v2 p0
         (HP1:Ir.ptr (Ir.pphy o I cid) = v1)
         (HGEPINBS:gepinbs m v1 v2 p0),
    ~ exists l2 o2, v2 = Ir.ptr (Ir.plog l2 o2).
Proof.
  intros.
  generalize dependent o.
  generalize dependent I.
  generalize dependent cid.
  induction HGEPINBS.
  { intros. inv HP1. intros HH. inv HH. inv H0. inv H1.
    unfold Ir.SmallStep.gep in *. des_ifs.
  }
  { intros. intros HH. inv HH. inv H. inv H0.
    unfold Ir.SmallStep.gep in HP1.
    des_ifs.
    exploit IHHGEPINBS. ss. do 3 eexists. ss. eauto.
    exploit IHHGEPINBS. ss. do 3 eexists. ss.
  }
  { intros. intros HH. inv HH. inv H.
    unfold Ir.SmallStep.gep in H0.
    des_ifs.
    exploit IHHGEPINBS. ss. eexists. eexists. eexists. ss.
  }
Qed.

Lemma gepinbs_phy_samecid:
  forall m v1 v2 o1 o2 I1 I2 cid1 cid2 p0
         (HP1:Ir.ptr (Ir.pphy o1 I1 cid1) = v1)
         (HP1:Ir.ptr (Ir.pphy o2 I2 cid2) = v2)
         (HGEPINBS:gepinbs m v1 v2 p0),
    cid1 = cid2.
Proof.
  intros.
  generalize dependent o1.
  generalize dependent o2.
  generalize dependent I1.
  generalize dependent I2.
  generalize dependent cid1.
  generalize dependent cid2.
  induction HGEPINBS.
  { intros. inv HP1.
    unfold Ir.SmallStep.gep in *. des_ifs.
  }
  { intros. inv HP0.
    unfold Ir.SmallStep.gep in HP1.
    des_ifs.
    exploit IHHGEPINBS. ss. ss. eauto.
    exploit IHHGEPINBS. ss. ss. eauto.
  }
  { intros. inv HP0.
    unfold Ir.SmallStep.gep in *. des_ifs.
    exploit IHHGEPINBS. ss. ss. eauto.
    exploit IHHGEPINBS. ss. ss. eauto.
  }
Qed.

Lemma gep_phy_Ilb:
  forall o1 o2 I1 I2 cid1 cid2 ofs t m
         (HMIN:exists n, list_min n I1)
         (HGEP:(Ir.ptr (Ir.pphy o2 I2 cid2)) =
               Ir.SmallStep.gep (Ir.pphy o1 I1 cid1) ofs t m true)
         (HPOS:posofs ofs t),
  exists n, (list_min n (o1::I1) /\ list_min n I2).
Proof.
  intros.
  unfold Ir.SmallStep.gep in HGEP.
  unfold posofs in HPOS.
  rewrite <- Nat.ltb_lt in HPOS.
  rewrite HPOS in HGEP.
  des_ifs.
  rewrite Nat.ltb_lt in *.
  unfold Ir.SmallStep.twos_compl_add.
  unfold Ir.SmallStep.twos_compl.
  rewrite Nat.mod_small.
  unfold list_min.
  simpl.
  inv HMIN. inv H.
  destruct (x <=? o1) eqn:HEQ.
  { rewrite Nat.leb_le in HEQ.
    exists x.
    split. split. eauto.
    simpl. constructor. ss. ss.
    split. do 2 right. ss.
    constructor. ss. constructor. lia. ss.
  }
  { rewrite Nat.leb_gt in HEQ.
    exists o1. split. split. eauto. constructor. ss.
    rewrite List.Forall_forall in *. intros. eapply H1 in H. lia.
    split. eauto.
    constructor. ss. constructor. lia.
    rewrite List.Forall_forall in *. intros. eapply H1 in H. lia.
  }
  rewrite Ir.PTRSZ_MEMSZ.
  ss.
Qed.

Lemma gep_phy_Iub:
  forall o1 o2 I1 I2 cid1 cid2 ofs t m
         (HMAX:list_max o1 I1)
         (HGEP:(Ir.ptr (Ir.pphy o2 I2 cid2)) =
               Ir.SmallStep.gep (Ir.pphy o1 I1 cid1) ofs t m true)
         (HPOS:posofs ofs t),
  list_max o2 I2.
Proof.
  intros.
  unfold Ir.SmallStep.gep in HGEP.
  unfold posofs in HPOS.
  rewrite <- Nat.ltb_lt in HPOS.
  rewrite HPOS in HGEP.
  des_ifs.
  rewrite Nat.ltb_lt in *.
  unfold Ir.SmallStep.twos_compl_add.
  unfold Ir.SmallStep.twos_compl.
  rewrite Nat.mod_small.
  unfold list_max.
  simpl.
  inv HMAX.
  split.
  right. left. ss.
  constructor. lia. constructor. ss.
  rewrite List.Forall_forall in *. intros. apply H0 in H1. lia.
  rewrite Ir.PTRSZ_MEMSZ.
  ss.
Qed.

Lemma gepinbs_log_sameblk:
  forall m v1 l1 o1 l2 o2 v2 p0
         (HP1:Ir.ptr (Ir.plog l1 o1) = v1)
         (HP2:Ir.ptr (Ir.plog l2 o2) = v2)
         (HGEPINBS:gepinbs m v1 v2 p0),
    l1 = l2.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent o1.
  generalize dependent o2.
  induction HGEPINBS.
  { intros. inv HP2. unfold Ir.SmallStep.gep in *. des_ifs. }
  { intros.
    unfold Ir.SmallStep.gep in HGEP1.
    des_ifs. exploit IHHGEPINBS. ss. eexists. eauto.
  }
  { intros. unfold Ir.SmallStep.gep in HGEP1.
    des_ifs.
    exploit IHHGEPINBS. ss. do 3 eexists. ss.
  }
Qed.

Lemma gepinbs_notnum:
  forall m v1 v2 p0
         (HGEPINBS:gepinbs m v1 v2 p0),
    (~ (exists n1, v1 = Ir.num n1)) /\
    (~ (exists n2, v2 = Ir.num n2)).
Proof.
  intros.
  induction HGEPINBS.
  { split. intros HH. inv HH. unfold Ir.SmallStep.gep in *. des_ifs.
    intros HH. inv HH. unfold Ir.SmallStep.gep in *.  des_ifs. }
  { inv IHHGEPINBS.
    split; try ss.
    intros HH.
    inv HH.
    unfold Ir.SmallStep.gep in H1. des_ifs. }
  { inv IHHGEPINBS.
    split; try ss.
    intros HH. inv HH.
    unfold Ir.SmallStep.gep in H1. des_ifs. }
Qed.

Lemma gepinbs_icmp_det:
  forall m v1 v2 p1 p2 p0
         (HP1:Ir.ptr p1 = v1)
         (HP2:Ir.ptr p2 = v2)
         (HGEPINBS:gepinbs m v1 v2 p0),
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 m = false.
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  destruct v1; try congruence.
  destruct p; try (inv HP1; reflexivity).
  inv HP1.
  destruct p2; try reflexivity.
  eapply gepinbs_log_sameblk in HGEPINBS; try reflexivity.
  subst b.
  rewrite Nat.eqb_refl. simpl. des_ifs.
Qed.

Lemma phys_minmaxI_cons:
  forall o I1 I2 cid i
    (HPMM:phys_minmaxI (Ir.pphy o I1 cid) (Ir.pphy o I2 cid)),
    phys_minmaxI (Ir.pphy o (i::I1) cid) (Ir.pphy o (i::I2) cid).
Proof.
  intros.
  unfold phys_minmaxI in *.
  inv HPMM. inv H. inv H0. inv H. inv H0. inv H.
  inv H0. inv H1. inv H2. inv H3. inv H4.
  inv H. inv H0.
  exploit list_minmax_le.
  eapply H1. eapply H3. intros HH.
  do 4 eexists.
  destruct (x3 <=? i) eqn:HMIN.
  { rewrite Nat.leb_le in HMIN.
    destruct (i <? x4) eqn:HMAX.
    { rewrite Nat.ltb_lt in HMAX.
      exists x3. exists x4.
      split. ss. split. ss.
      split. eapply list_min_cons; ss.
      split. eapply list_min_cons; ss.
      split. eapply list_max_cons. ss. omega.
      eapply list_max_cons. ss. omega.
    }
    { rewrite Nat.ltb_ge in HMAX.
      exists x3. exists i.
      split. ss. split. ss.
      split. eapply list_min_cons; ss.
      split. eapply list_min_cons; ss.
      split. eapply list_max_cons2. eassumption. ss.
      eapply list_max_cons2. eassumption. omega.
    }
  }
  { rewrite Nat.leb_gt in HMIN.
    destruct (i <? x4) eqn:HMAX.
    { rewrite Nat.ltb_lt in HMAX.
      exists i. exists x4.
      split. ss. split. ss.
      split. eapply list_min_cons2. eassumption. omega.
      split. eapply list_min_cons2. eassumption. omega.
      split. eapply list_max_cons. ss. omega.
      eapply list_max_cons. ss. omega.
    }
    { rewrite Nat.ltb_ge in HMAX.
      omega.
    }
  }
Qed.

Lemma phys_minmaxI_refl:
  forall o I s i
    (HIN:List.In i I),
    phys_minmaxI (Ir.pphy o I s) (Ir.pphy o I s).
Proof.
  unfold phys_minmaxI.
  intros.
  destruct I. inv HIN.
  assert (HH1 := list_min_exists n I).
  assert (HH2 := list_max_exists n I).
  inv HH1. inv HH2.
  do 6 eexists.
  split. ss.
  split. ss.
  do 4 (split; try eassumption).
Qed.

Lemma twos_compl_add_PTRSZ:
  forall o i
         (HLE:o + i < Ir.MEMSZ),
  Ir.SmallStep.twos_compl_add o i Ir.PTRSZ = o + i.
Proof.
  intros.
  unfold Ir.SmallStep.twos_compl_add.
  unfold Ir.SmallStep.twos_compl.
  rewrite Ir.PTRSZ_MEMSZ.
  rewrite Nat.mod_small. ss.
  ss.
Qed.

Lemma twos_compl_add_PTRSZ':
  forall o i
         (HLE:o + i <? Ir.MEMSZ = true),
  Ir.SmallStep.twos_compl_add o i Ir.PTRSZ = o + i.
Proof.
  intros.
  apply twos_compl_add_PTRSZ.
  rewrite <- Nat.ltb_lt. ss.
Qed.

Lemma gepinbs_phy_Imax:
  forall m o I1 cid p1 p2 p0 o0 I0 cid0
         (HP1:p1 = (Ir.ptr (Ir.pphy o I1 cid)))
         (HP0:p0 = Ir.pphy o0 I0 cid0)
         (HGEP:gepinbs m p1 p2 p0),
    (exists n, list_max n I1 /\ list_max n I0 /\ o < n) \/
    (list_max o I1 /\ (forall n, list_max n I0 -> n <= o)).
Proof.
  intros.
  generalize dependent o.
  generalize dependent I1.
  generalize dependent I0.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1.
    destruct I0.
    { right.
      unfold Ir.SmallStep.gep in *.
      unfold posofs in *. rewrite <- Nat.ltb_lt in HPOS1, HPOS2.
      des_ifs.
      split.
      {
        split.
        {
          apply list_max_cons. apply list_max_one.
          rewrite twos_compl_add_PTRSZ. lia.
          rewrite Nat.ltb_lt in Heq. ss.
        }
        {
          apply list_max_cons. apply list_max_one.
          rewrite twos_compl_add_PTRSZ. lia.
          rewrite Nat.ltb_lt in Heq. ss.
        }
      }
      { intros. inv H. inv H0. }
    }
    assert (HMAX := list_max_exists n I0).
    inv HMAX.
    destruct (x <=? o) eqn:HLE.
    { right.
      split.
      {
        unfold posofs in *. rewrite <- Nat.ltb_lt in *.
        unfold Ir.SmallStep.gep in *.
        des_ifs.
        split.
        apply list_max_cons. eapply list_max_cons2. eapply H0.
        rewrite Nat.leb_le in HLE. lia.
        rewrite twos_compl_add_PTRSZ. lia.
        rewrite Nat.ltb_lt in *. ss.
        apply list_max_cons. eapply list_max_cons2. eapply H0.
        rewrite Nat.leb_le in HLE. lia.
        rewrite twos_compl_add_PTRSZ. lia.
        rewrite Nat.ltb_lt in *. ss.
      }
      { intros. eapply list_max_inj_l with (n := x) in H1; try ss.
        rewrite Nat.leb_le in HLE. omega. }
    }
    { left. exists x.
      unfold posofs in *. rewrite <- Nat.ltb_lt in *.
      unfold Ir.SmallStep.gep in *.
      des_ifs.
      split.
      {
        apply list_max_cons. apply list_max_cons. ss.
        rewrite Nat.leb_gt in HLE.
        omega.
        rewrite Nat.leb_gt in HLE.
        rewrite twos_compl_add_PTRSZ in HLE. eapply le_trans.
        instantiate (1 := o0 + ofs1 * Ir.ty_bytesz t1).
        eapply Nat.le_add_r.
        rewrite Nat.ltb_lt in Heq. omega.
        rewrite Nat.ltb_lt in Heq. ss.
      }
      { split. ss.
        apply Nat.leb_gt in HLE.
        apply Nat.ltb_lt. ss.
      }
    }
  }
  { intros.
    inv HP0.
    unfold posofs in HPOS.
    rewrite <- Nat.ltb_lt in HPOS.
    unfold Ir.SmallStep.gep in HP1.
    des_ifs.
    exploit IHHGEP.
    ss. ss. intros HH. inv HH.
    { inv H. inv H0. inv H1. clear IHHGEP.
      remember (Ir.SmallStep.twos_compl_add n (ofs * Ir.ty_bytesz t)
                                            Ir.PTRSZ) as n'.
      destruct (x <=? n') eqn:HLE.
      { rewrite Nat.leb_le in HLE.
        right. split.
        apply list_max_cons. eapply list_max_cons2. eapply H. ss.
        subst n'.
        rewrite twos_compl_add_PTRSZ.
        apply Nat.le_add_r. rewrite Nat.ltb_lt in Heq. ss.
        intros. apply list_max_inj_l with (n := x) in H1. omega. ss.
      }
      { left.
        exists x.
        split.
        {  apply list_max_cons. apply list_max_cons. ss.
          subst n'.
          rewrite Nat.leb_gt in HLE. rewrite twos_compl_add_PTRSZ in *. omega.
          rewrite Nat.ltb_lt in Heq. omega.
          rewrite Nat.ltb_lt in Heq. omega.
          subst n'.
          rewrite Nat.leb_gt in HLE. rewrite twos_compl_add_PTRSZ in *.
          lia. rewrite Nat.ltb_lt in Heq. ss.
        }
        { split. ss. rewrite Nat.leb_gt in HLE. omega. }
      }
    }
    { inv H. right.
      split.
      { apply list_max_cons. eapply list_max_cons2. eassumption.
        rewrite twos_compl_add_PTRSZ.
        apply Nat.le_add_r. rewrite Nat.ltb_lt in Heq. ss.
        rewrite twos_compl_add_PTRSZ.
        apply Nat.le_add_r. rewrite Nat.ltb_lt in Heq. ss.
      }
      { intros. apply H1 in H.
        rewrite twos_compl_add_PTRSZ'. lia.
        ss.
      }
    }
  }
  { intros. inv HP1. eapply IHHGEP. ss. ss. }
Qed.

Lemma gepinbs_sym:
  forall m p1 p2 p0
         (HGEP:gepinbs m p1 p2 p0),
    gepinbs m p2 p1 p0.
Proof.
  intros.
  induction HGEP.
  { eapply gi_one. eassumption. eassumption. ss. ss. }
  { eapply gi_succ_r. eassumption. eassumption. ss. }
  { eapply gi_succ_l. eassumption. eassumption. ss. }
Qed.

Lemma gepinbs_phy_I_In:
  forall m p1 p2 p0 o I cid
         (HP1:p1 = Ir.ptr (Ir.pphy o I cid))
         (HGEP:gepinbs m p1 p2 p0),
    List.In o I.
Proof.
  intros.
  generalize dependent o.
  generalize dependent I.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1. unfold Ir.SmallStep.gep in *.
    des_ifs. right. left. ss. right. left. ss. }
  { intros. inv HP1. unfold Ir.SmallStep.gep in *.
    des_ifs. right. left. ss. right. left. ss. }
  { intros. eapply IHHGEP. eassumption. }
Qed.

Lemma gepinbs_phy_Imin:
  forall m o I1 cid p1 p2 p0 o0 I0
         (HP1:p1 = (Ir.ptr (Ir.pphy o I1 cid)))
         (HP0:p0 = Ir.pphy o0 I0 cid)
         (HGEP:gepinbs m p1 p2 p0),
    (exists n, list_min n I1 /\ list_min n I0) \/
     list_min o0 I1.
Proof.
  intros.
  generalize dependent o.
  generalize dependent o0.
  generalize dependent I1.
  generalize dependent I0.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1. unfold Ir.SmallStep.gep in H.
    unfold posofs in *. rewrite <- Nat.ltb_lt in HPOS1, HPOS2. des_ifs.
    { destruct I0.
      { right. eapply list_min_cons2.
        apply list_min_one.
        rewrite twos_compl_add_PTRSZ'. apply Nat.le_add_r.
        ss.
      }
      { assert (HH := list_min_exists n I0).
        inv HH.
        destruct (x <? o0) eqn:HLE.
        { left. exists x.
          split; try ss.
          apply list_min_cons.
          apply list_min_cons.
          ss.
          rewrite twos_compl_add_PTRSZ'. rewrite Nat.ltb_lt in HLE.
          lia. ss.
          rewrite Nat.ltb_lt in HLE. omega.
        }
        { destruct (x <=? Ir.SmallStep.twos_compl_add o0 (ofs1 * Ir.ty_bytesz t1)
                          Ir.PTRSZ)
                   eqn:HLE2.
          { right. rewrite Nat.ltb_ge in HLE.
            eapply list_min_cons2.
            apply list_min_cons.
            eassumption.
            rewrite Nat.leb_le in HLE2. ss. ss. }
          { rewrite Nat.ltb_ge in HLE. rewrite Nat.leb_gt in HLE2.
            right. eapply list_min_cons2.
            eapply list_min_cons2.
            eassumption.
            omega.
            rewrite twos_compl_add_PTRSZ'. lia.
            ss.
          }
        }
      }
    }
  }
  { intros. inv HP0. dup HP1.
    unfold Ir.SmallStep.gep in HP1. dup HPOS. unfold posofs in HPOS.
    rewrite <- Nat.ltb_lt in HPOS.
    des_ifs.
    exploit IHHGEP. ss. ss. intros HH.
    inv HH.
    { inv H. inv H0. left.
      symmetry in HP0.
      dup HP0.
      apply gep_phy_Ilb in HP0.
      inv HP0. inv H0. 
      apply list_min_In in H2.
      exists x0.
      assert (x = x0).
      { eapply list_min_inj_l. eapply H.  eapply H2. }
      subst x.
      split.
      ss. ss. eapply gepinbs_phy_I_In. ss. eassumption.
      eexists. eassumption. assumption.
    }
    { symmetry in HP0.
      apply gep_phy_Ilb in HP0.
      inv HP0. inv H0.
      apply list_min_In in H1.
      assert (x = o0).
      { eapply list_min_inj_l. eapply H1. eassumption. }
      subst x.
      right. ss.
      eapply gepinbs_phy_I_In. ss. eassumption.
      eexists. eapply H.
      ss.
    }
  }
  { intros. inv HP0. inv HP1.
    exploit IHHGEP. ss. ss. eauto. }
Qed.

Lemma gepinbs_phy_Imin2:
  forall m o I1 cid p1 p2 p0 o0 I0 n
         (HP1:p1 = (Ir.ptr (Ir.pphy o I1 cid)))
         (HP0:p0 = Ir.pphy o0 I0 cid)
         (HGEP:gepinbs m p1 p2 p0)
         (HMIN:list_min n I1),
    n <= o.
Proof.
  intros.
  generalize dependent o.
  generalize dependent o0.
  generalize dependent I1.
  generalize dependent I0.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1. unfold Ir.SmallStep.gep in H.
    unfold posofs in *. rewrite <- Nat.ltb_lt in HPOS1, HPOS2. des_ifs.
    inv HMIN. rewrite List.Forall_forall in H0.
        exploit H0. right. ss. left. ss.
        intros. ss.
  }
  { intros. inv HP0.
    unfold Ir.SmallStep.gep in HP1. unfold posofs in HPOS.
    rewrite <- Nat.ltb_lt in HPOS.
    des_ifs.
    inv HMIN. rewrite List.Forall_forall in H0.
    exploit H0. right. left. ss. intros. omega.
  }
  { ss. }
Qed.

Lemma gepinbs_phy_base:
  forall m o1 I1 cid p1 p2 p0
         (HP1:p1 = (Ir.ptr (Ir.pphy o1 I1 cid)))
         (HGEP:gepinbs m p1 p2 p0),
    exists o2 I2, p0 = Ir.pphy o2 I2 cid.
Proof.
  intros.
  generalize dependent o1.
  generalize dependent I1.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1. unfold Ir.SmallStep.gep in H.
    des_ifs; do 3 eexists; ss.
  }
  { intros. inv HP1. unfold Ir.SmallStep.gep in H.
    des_ifs.
    exploit IHHGEP. ss. eauto.
    exploit IHHGEP. ss. eauto.
  }
  { ss. }
Qed.

Lemma gepinbs_phy_Imin3:
  forall m o1 o2 I1 cid p1 p2 p0 I2
         (HP1:p1 = (Ir.ptr (Ir.pphy o1 I1 cid)))
         (HP2:p2 = (Ir.ptr (Ir.pphy o2 I2 cid)))
         (HGEP:gepinbs m p1 p2 p0),
    exists n, list_min n I1 /\ list_min n I2.
Proof.
  intros.
  generalize dependent o1.
  generalize dependent o2.
  generalize dependent I1.
  generalize dependent I2.
  generalize dependent cid.
  induction HGEP.
  { intros. inv HP1. inv HP2. unfold Ir.SmallStep.gep in *.
    unfold posofs in HPOS1, HPOS2. rewrite <- Nat.ltb_lt in HPOS1, HPOS2. des_ifs.
    assert (HH2 := list_min_exists n l).
    inv HH2.
    exists x. split.
    apply list_min_swap.
    apply list_min_cons. ss. rewrite twos_compl_add_PTRSZ'.
    apply list_min_hd in H. lia.
    ss.
    apply list_min_swap.
    apply list_min_cons.  ss.
    rewrite twos_compl_add_PTRSZ'. apply list_min_hd in H. lia. ss.
  }
  { intros. inv HP1. inv HP2. dup H. dup HPOS.
    unfold Ir.SmallStep.gep in H. unfold posofs in HPOS.
    rewrite <- Nat.ltb_lt in HPOS.
    des_ifs.
    exploit IHHGEP. ss. ss. intros HH.
    inv HH. inv H.
    exists x. split; try assumption.
    dup HGEP. eapply gepinbs_phy_base in HGEP0; try reflexivity.
    inv HGEP0. inv H.
    assert (x <= n).
    { eapply gepinbs_phy_Imin2. ss. ss. eassumption. ss. }
    apply list_min_cons; try omega.
    apply list_min_cons.
    ss.
    rewrite twos_compl_add_PTRSZ'. lia. ss.
  }
  { intros.
    inv HP2. inv HP1.
    unfold Ir.SmallStep.gep in H. unfold posofs in HPOS. rewrite <- Nat.ltb_lt in HPOS.
    des_ifs.
    exploit IHHGEP. ss. ss. intros HH.
    inv HH. inv H.
    exists x. split; try assumption.
    dup HGEP. eapply gepinbs_phy_base in HGEP; try reflexivity.
    inv HGEP. inv H.
    assert (x <= n).
    { eapply gepinbs_phy_Imin2. ss. ss. apply gepinbs_sym in HGEP0.
      eassumption. ss. }
    apply list_min_cons; try omega.
    apply list_min_cons. ss.
    rewrite twos_compl_add_PTRSZ'. lia. ss.
  }
Qed.

Lemma gep_phy_Iub2:
  forall o I cid o' I' cid' ofs t m
         (HGEP:Ir.SmallStep.gep (Ir.pphy o I cid) ofs t m true = Ir.ptr (Ir.pphy o' I' cid'))
         (HPOS:posofs ofs t),
    list_max o' I' \/ (exists n, list_max n I /\ list_max n I').
Proof.
  intros.
  destruct I.
  { left.
    unfold Ir.SmallStep.gep in HGEP.
    unfold posofs in HPOS.
    des_ifs.
    { unfold Ir.SmallStep.twos_compl_add.
      unfold Ir.SmallStep.twos_compl.
      unfold list_max. split.
      right. constructor. ss.
      constructor. rewrite Nat.mod_small. lia.
      rewrite Ir.PTRSZ_MEMSZ. rewrite Nat.ltb_lt in Heq0. ss.
      constructor. ss.
      constructor.
    }
    { rewrite Nat.ltb_ge in Heq. omega. }
  }
  { assert (HH := list_max_exists n I).
    inv HH.
    unfold Ir.SmallStep.gep in HGEP.
    des_ifs.
    { destruct (x <=? Ir.SmallStep.twos_compl_add o (ofs * Ir.ty_bytesz t) Ir.PTRSZ)
               eqn:HLE.
      { left.
        constructor.
        right. left. ss.
        constructor. rewrite twos_compl_add_PTRSZ. lia.
          rewrite Nat.ltb_lt in Heq0. ss.
        constructor. ss.
        inv H.
        rewrite List.Forall_forall in *.
        intros. apply H1 in H. rewrite Nat.leb_le in HLE.
          rewrite twos_compl_add_PTRSZ. eapply Nat.le_trans. eapply H.
          rewrite twos_compl_add_PTRSZ in HLE. ss.
          rewrite Nat.ltb_lt in Heq0. ss. rewrite Nat.ltb_lt in Heq0. ss.
      }

      { right. exists x.
        split. ss.
        rewrite Nat.leb_gt in HLE.
        rewrite twos_compl_add_PTRSZ in HLE.
        constructor. right. right. inv H. ss.
        constructor. 
        lia.
        constructor. rewrite twos_compl_add_PTRSZ. lia.
        rewrite Nat.ltb_lt in Heq0. lia.
        inv H. rewrite List.Forall_forall in *.
        intros. apply H1 in H. ss.
        rewrite Nat.ltb_lt in Heq0. ss.
      }
    }
    { unfold posofs in HPOS. rewrite Nat.ltb_ge in Heq. omega. }
  }
Qed.

Theorem gepinbs_after_icmpeq_true:
  forall md st st' r ptrty op1 op2 v1 v2 e pbase
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iicmp_eq r ptrty op1 op2) = Ir.Config.cur_inst md st)
    (HOP1:Some v1 = Ir.Config.get_val st op1)
    (HOP2:Some v2 = Ir.Config.get_val st op2)
    (* gepinbs holds *)
    (HEQPROP:gepinbs (Ir.Config.m st) v1 v2 pbase)
    (* have a small step *)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st'))
    (* p1 == p2 is true *)
    (HTRUE:Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r)),

    v1 = v2 \/
    (exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2).
Proof.
  intros.
  inv HSTEP; try congruence.
  { inv HISTEP;try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite <- HINST in HNEXT.
      rewrite <- HOP1, <- HOP2 in HNEXT.
      dup HEQPROP. apply gepinbs_notnum in HEQPROP0.
      inv HEQPROP0.
      destruct v1.
      { exfalso. eapply H. eexists. ss. }
      destruct v2.
      { exfalso. eapply H0. eexists. ss. }
      des_ifs.
      clear H H0.
      destruct p.
      { (* log *)
        destruct p0.
        { dup HEQPROP.
          eapply gepinbs_log_sameblk in HEQPROP; try reflexivity.
          subst b0.
          unfold Ir.SmallStep.icmp_eq_ptr in Heq. rewrite Nat.eqb_refl in Heq.
          inv Heq.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          unfold Ir.SmallStep.to_num in HTRUE.
          des_ifs. rewrite Nat.eqb_eq in Heq. subst n.
          left. ss.
          { unfold Ir.Config.cur_inst in HINST.
            unfold Ir.Config.cur_fdef_pc in HINST.
            des_ifs. }
        }
        { (* cannot be phy *)
          eapply gepinbs_log_neverphy in HEQPROP; try reflexivity.
          exfalso. apply HEQPROP. do 3 eexists. ss.
        }
      }
      { (* phy *)
        destruct p0.
        { (* cannot be log *)
          eapply gepinbs_phy_neverlog in HEQPROP; try reflexivity.
          exfalso. apply HEQPROP. do 3 eexists.
        }
        { right.
          unfold Ir.SmallStep.icmp_eq_ptr in Heq.
          unfold Ir.SmallStep.p2N in Heq.
          rewrite Nat.min_id in Heq.
          unfold Ir.SmallStep.twos_compl in Heq.
          rewrite Ir.PTRSZ_MEMSZ in Heq.
          rewrite Nat.mod_small in Heq.
          inv Heq.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          unfold Ir.SmallStep.to_num in HTRUE.
          inv HTRUE.
          des_ifs.
          rewrite Nat.eqb_eq in Heq. subst n.
          dup HEQPROP.
          eapply gepinbs_phy_samecid in HEQPROP0; try reflexivity.
          subst o.
          dup HEQPROP. eapply gepinbs_phy_base in HEQPROP0; try reflexivity.
          inv HEQPROP0. inv H.
          eexists. eexists. split. ss. split. ss.
          unfold phys_minmaxI.
          dup HEQPROP.
          eapply gepinbs_phy_Imin3 in HEQPROP0; try reflexivity.
          dup HEQPROP.
          eapply gepinbs_phy_Imax in HEQPROP1.
          2: ss. 2: ss.
          apply gepinbs_sym in HEQPROP.
          eapply gepinbs_phy_Imax in HEQPROP.
          2:ss. 2:ss.
          inv HEQPROP0. inv H.
          inv HEQPROP.
          { inv H. inv H3. inv H4.
            inv HEQPROP1.
            { inv H4. inv H6. inv H7.
              assert (x2 = x3).
              { eapply list_max_inj_l. eapply H3. ss. }
              subst x2.
              do 6 eexists.
              split. ss. split. ss.
              split. eassumption.
              split. ss.
              split. eassumption.
              ss.
            }
            { inv H4. apply H7 in H3.
              omega. }
          }
          { inv H.
            inv HEQPROP1.
            { inv H. inv H5. inv H6. apply H4 in H5. omega. }
            { inv H. 
              do 6 eexists.
              split. ss. split. ss.
              split. eassumption. split. ss.
              split. eassumption. ss.
            }
          }
          { unfold Ir.Config.cur_inst in HINST. unfold Ir.Config.cur_fdef_pc in HINST.
            des_ifs.
          }
          { inv HWF.
            exploit wf_ptr. rewrite <- HOP2. reflexivity.
            intros HH.
            unfold Ir.Config.ptr_wf in HH.
            inv HH. eapply H0. reflexivity.
          }
        }
      }
      { inv HNEXT.
        rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
        unfold Ir.Config.get_val in HTRUE.
        rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
        inv HTRUE.
        unfold Ir.Config.cur_inst in HINST. unfold Ir.Config.cur_fdef_pc in HINST.
            des_ifs.
      }
      { inv HNEXT.
        rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
        unfold Ir.Config.get_val in HTRUE.
        rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
        inv HTRUE.
        unfold Ir.Config.cur_inst in HINST. unfold Ir.Config.cur_fdef_pc in HINST.
            des_ifs.
      }
    }
    { eapply gepinbs_icmp_det in HEQPROP.
      rewrite HNONDET in HEQPROP. inv HEQPROP.
      congruence. congruence.
    }
  }
  { unfold Ir.SmallStep.t_step in HTSTEP.
    apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    des_ifs.
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
  rewrite List.Forall_forall in *.
  dup H.
  apply H1 in H4. apply H3 in H. omega.
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

Lemma phys_minmaxI_get_deref:
  forall m p q sz
         (HWF:Ir.Memory.wf m)
         (HPMM:phys_minmaxI p q)
         (HSZ:sz > 0),
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
  assert (HE1:exists xm, list_min xm (x :: (x+sz) :: x0) /\
                         list_min xm (x :: (x+sz) :: x1)).
  { destruct (x <=? x3) eqn:HLE.
    { exists x.
      split.
      { unfold list_min in *. split. left. ss.
        rewrite List.Forall_forall. intros.
        inv H1. rewrite Nat.leb_le in HLE. inv H5.
        { omega. }
        inv H.
        { omega. }
        rewrite List.Forall_forall in H7.
        apply H7 in H0. omega.
      }
      { unfold list_min in *. split. left. ss.
        rewrite List.Forall_forall. intros.
        inv H2. rewrite Nat.leb_le in HLE. inv H5.
        { omega. }
        inv H.
        { omega. }
        rewrite List.Forall_forall in H7.
        apply H7 in H0. omega.
      }
    }
    { rewrite Nat.leb_gt in HLE.
      exists x3.
      unfold list_min in *.
      inv H1. inv H2.
      repeat (rewrite List.Forall_forall in *).
      split.
      { split. right. right. ss.
        intros. inv H1. omega. inv H2. omega. apply H6. ss.
      }
      { split. right. right. ss.
        intros. inv H1. omega. inv H2. omega. apply H0. ss.
      }
    }
  }
  assert (HE2:exists xm, list_max xm (x :: (x+sz) :: x0) /\
                         list_max xm (x :: (x+sz) :: x1)).
  { destruct (x4 <=? x + sz) eqn:HLE.
    { exists (x + sz).
      split.
      { unfold list_max in *. split. right. left. ss.
        rewrite List.Forall_forall. intros.
        inv H3. rewrite Nat.leb_le in HLE. inv H5.
        { omega. }
        inv H.
        { omega. }
        rewrite List.Forall_forall in H7.
        apply H7 in H0. omega.
      }
      { unfold list_max in *. split. right. left. ss.
        rewrite List.Forall_forall. intros.
        inv H5.
        { omega. }
        inv H6.
        { omega. }
        rewrite Nat.leb_le in HLE.
        rewrite List.Forall_forall in H4.
        inv H4.
        apply H5 in H. omega.
      }
    }
    { rewrite Nat.leb_gt in HLE.
      exists x4.
      unfold list_max in *.
      inv H3. inv H4.
      repeat (rewrite List.Forall_forall in *).
      split.
      { split. right. right. ss.
        intros. inv H3. omega. inv H4. omega. apply H6. ss.
      }
      { split. right. right. ss.
        intros. inv H3. omega. inv H4. omega. apply H0. ss.
      }
    }
  }
  clear H1 H2 H3 H4.
  inv HE1. inv H1. inv HE2. inv H1.

  assert (HINB1:
            Ir.Memory.inbounds_blocks2 m (x :: x + sz :: x0) =
            Ir.Memory.inbounds_blocks2 m [x5;x6]).
  { eapply inbounds_blocks2_minmax. ss. ss. ss. ss.
    exploit list_minmax_lt. eapply H. eapply H2.
    left. ss. right. left. ss. omega.
    intros. omega. }
  assert (HINB2:
            Ir.Memory.inbounds_blocks2 m (x :: x + sz :: x1) =
            Ir.Memory.inbounds_blocks2 m [x5;x6]).
  { eapply inbounds_blocks2_minmax. ss. ss. ss. ss.
    exploit list_minmax_lt. eapply H. eapply H2.
    left. ss. right. left. ss. omega.
    intros. omega. }
  rewrite HINB1, HINB2.
  reflexivity.
Qed.




(* ends with refinement with common update_reg_and_incrpc calls *)
Ltac thats_it :=
          eapply Ir.SSRefinement.refines_update_reg_and_incrpc;
          [ eassumption | eassumption
          | apply Ir.Refinement.refines_state_eq;
            apply Ir.Config.eq_refl
          | try apply Ir.Refinement.refines_value_refl; try constructor; fail ].

Ltac cc_thats_it := constructor; constructor; thats_it.


(* ends with refinement with common incrpc calls *)
Ltac thats_it2 :=
          eapply Ir.SSRefinement.refines_incrpc;
          [ eassumption | eassumption
          | apply Ir.Refinement.refines_state_eq;
            apply Ir.Config.eq_refl ].

Ltac cc_thats_it2 := constructor; constructor; thats_it2.

Ltac hey_terminator HINST2 :=
  apply Ir.Config.cur_inst_not_cur_terminator in HINST2;
       congruence.

Ltac hey_terminator2 HINST2 HTSTEP :=
  apply Ir.Config.cur_inst_not_cur_terminator in HINST2;
       unfold Ir.SmallStep.t_step in HTSTEP;
       des_ifs.

Ltac unfold_phys_minmaxI H :=
  unfold phys_minmaxI in H;
  destruct H as [o H];
  destruct H as [I1 H];
  destruct H as [I2 H];
  destruct H as [cid H];
  destruct H as [ofsmin H];
  destruct H as [ofsmax H];
  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].




(*****
      Refinement on load instruction.
 *****)

Theorem load_refines:
  forall md1 md2 (* md2 is an optimized program *)
         st r retty opptr1 opptr2 v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two loads on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iload r retty opptr1) = Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iload r retty opptr2) = Ir.Config.cur_inst md2 st)
         (* Has a good relation between pointer operands *)
         (HOP1:Ir.Config.get_val st opptr1 = Some v1)
         (HOP2:Ir.Config.get_val st opptr2 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),

    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.

      clear wf_cid_to_f.
      clear wf_cid_to_f2.
      clear wf_stack.
      clear wf_ptr.
      clear wf_ptr_mem.

      inv HPMM. inv H. inv H0. inv H1.
      unfold Ir.deref in *.
      unfold Ir.load_val in *.
      unfold Ir.load_bytes in *.
      rewrite phys_minmaxI_get_deref with (q := x0) in HNEXT.
      des_ifs; try (cc_thats_it).
      inv HWF2. ss. ss.
      apply Ir.ty_bytesz_pos.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on store instruction.
 *****)

Theorem store_refines:
  forall md1 md2 (* md2 is an optimized program *)
         st valty opptr1 opptr2 opval v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two stores on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.istore valty opptr1 opval) = Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.istore valty opptr2 opval) = Ir.Config.cur_inst md2 st)
         (* Has a good relation between pointer operands *)
         (HOP1:Ir.Config.get_val st opptr1 = Some v1)
         (HOP2:Ir.Config.get_val st opptr2 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
    intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.

      clear wf_cid_to_f.
      clear wf_cid_to_f2.
      clear wf_stack.
      clear wf_ptr.
      clear wf_ptr_mem.

      inv HPMM. inv H. inv H0. inv H1.
      unfold Ir.deref in *.
      rewrite phys_minmaxI_get_deref with (q := x0) in HNEXT.
      des_ifs.
      unfold Ir.store_val.
      unfold Ir.store_bytes.
      des_ifs; try (cc_thats_it2; fail);
      try (rewrite phys_minmaxI_get_deref with (q := x0) in *;
           [ congruence
           | inv HWF2; ss | ss
           | rewrite Nat.eqb_eq in Heq2; rewrite <- Heq2;  apply Ir.ty_bytesz_pos ]).
      { rewrite phys_minmaxI_get_deref with (q := x0) in *. rewrite Heq3 in Heq5.
        inv Heq5. cc_thats_it2.
        inv HWF2. ss.
        ss.
        rewrite Nat.eqb_eq in Heq2. rewrite <- Heq2.
        apply Ir.ty_bytesz_pos. }
      { rewrite phys_minmaxI_get_deref with (q := x0) in *. rewrite Heq3 in Heq5.
        inv Heq5. cc_thats_it2.
        inv HWF2. ss.
        ss.
        rewrite Nat.eqb_eq in Heq2. rewrite <- Heq2.
        apply Ir.ty_bytesz_pos. }
      constructor.
      cc_thats_it2.
      ss.
      ss.
      apply Ir.ty_bytesz_pos.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on free instruction.
 *****)

Theorem free_refines:
  forall md1 md2 (* md2 is an optimized program *)
         st opptr1 opptr2 v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two frees on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.ifree opptr1) = Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.ifree opptr2) = Ir.Config.cur_inst md2 st)
         (* Has a good relation between pointer operands *)
         (HOP1:Ir.Config.get_val st opptr1 = Some v1)
         (HOP2:Ir.Config.get_val st opptr2 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.

      clear wf_cid_to_f.
      clear wf_cid_to_f2.
      clear wf_stack.
      clear wf_ptr.
      clear wf_ptr_mem.

      inv HPMM. inv H. inv H0. inv H1.
      unfold Ir.SmallStep.free in *.
      dup H0.
      unfold_phys_minmaxI H1.
      subst x. subst x0.
      unfold Ir.deref in HNEXT, HNEXT0.
      rewrite phys_minmaxI_get_deref with (q := Ir.pphy o I2 cid) in HNEXT.
      des_ifs.
      cc_thats_it2. constructor. constructor. constructor.
      ss. ss. ss.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on ptrtoint instruction.
 *****)

Theorem ptrtoint_refines:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr2 retty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two ptrtoins on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iptrtoint r opptr1 retty) = Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iptrtoint r opptr2 retty) = Ir.Config.cur_inst md2 st)
         (* Has a good relation between pointer operands *)
         (HOP1:Ir.Config.get_val st opptr1 = Some v1)
         (HOP2:Ir.Config.get_val st opptr2 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.

      clear wf_cid_to_f.
      clear wf_cid_to_f2.
      clear wf_stack.
      clear wf_ptr.
      clear wf_ptr_mem.

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      des_ifs; try (cc_thats_it; fail).
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on psub instruction.
 *****)
Theorem psub_refines_l:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr11 opptr12 opptr2 retty ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two psubs on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.ipsub r retty ptrty opptr11 opptr2) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.ipsub r retty ptrty opptr12 opptr2) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr11 = Some v1)
         (HOP2:Ir.Config.get_val st opptr12 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.psub in *.
      des_ifs; try (cc_thats_it; fail).
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.

Theorem psub_refines_r:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr21 opptr22 retty ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two psubs on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.ipsub r retty ptrty opptr1 opptr21) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.ipsub r retty ptrty opptr1 opptr22) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr21 = Some v1)
         (HOP2:Ir.Config.get_val st opptr22 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.psub in *.
      des_ifs; try (cc_thats_it; fail).
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on icmp eq instruction.
 *****)

Theorem icmp_eq_refines_l:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr11 opptr12 opptr2 ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two icmps on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iicmp_eq r ptrty opptr11 opptr2) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iicmp_eq r ptrty opptr12 opptr2) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr11 = Some v1)
         (HOP2:Ir.Config.get_val st opptr12 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.icmp_eq_ptr in *.
      des_ifs; try (cc_thats_it; fail).

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP0. inv HOP0.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET. congruence.

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST1 in HCUR. inv HCUR.
      rewrite HOP1 in HOP0. inv HOP0.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET. congruence.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.

Theorem icmp_eq_refines_r:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr21 opptr22 ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two icmps on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iicmp_eq r ptrty opptr1 opptr21) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iicmp_eq r ptrty opptr1 opptr22) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr21 = Some v1)
         (HOP2:Ir.Config.get_val st opptr22 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
      Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.icmp_eq_ptr in *.
      des_ifs; try (cc_thats_it; fail).

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP3. inv HOP3.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET. des_ifs.

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST1 in HCUR. inv HCUR.
      rewrite HOP1 in HOP3. inv HOP3.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET. des_ifs.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on icmp ule instruction.
 *****)

Theorem icmp_ule_refines_l:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr11 opptr12 opptr2 ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two icmps on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iicmp_ule r ptrty opptr11 opptr2) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iicmp_ule r ptrty opptr12 opptr2) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr11 = Some v1)
         (HOP2:Ir.Config.get_val st opptr12 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.icmp_ule_ptr in *.
      des_ifs; try (cc_thats_it; fail).

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP0. inv HOP0.
      unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET. congruence.

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST1 in HCUR. inv HCUR.
      rewrite HOP1 in HOP0. inv HOP0.
      unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET. congruence.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.

Theorem icmp_ule_refines_r:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr21 opptr22 ptrty v1 v2 sr1 sr2
         (HWF1:Ir.Config.wf md1 st)
         (HWF2:Ir.Config.wf md2 st) (* State st is wellformed on two modules *)
         (* Two icmps on a same state(including same PC) *)
         (HINST1:Some (Ir.Inst.iicmp_ule r ptrty opptr1 opptr21) =
                 Ir.Config.cur_inst md1 st)
         (HINST2:Some (Ir.Inst.iicmp_ule r ptrty opptr1 opptr22) =
                 Ir.Config.cur_inst md2 st)
         (* Has a good relation between the first pointer operands *)
         (HOP1:Ir.Config.get_val st opptr21 = Some v1)
         (HOP2:Ir.Config.get_val st opptr22 = Some v2)
         (HPMM:exists p1 p2, Ir.ptr p1 = v1 /\ Ir.ptr p2 = v2 /\ phys_minmaxI p1 p2)
         (* And.. have a step. *)
         (HSTEP1:Ir.SmallStep.sstep md1 st sr1)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP1.
  { inv HSTEP2.
    { inv HISTEP; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST1 in HNEXT.
      rewrite HOP1 in HNEXT.
      inv HISTEP0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT0.
      rewrite <- HINST2 in HNEXT0.
      rewrite HOP2 in HNEXT0.
      inv HWF1.
      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      unfold Ir.SmallStep.icmp_ule_ptr in *.
      unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in *.
      des_ifs; try (cc_thats_it; fail).

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP3. inv HOP3.
      unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET. des_ifs.

      inv HPMM. inv H. inv H0. inv H1.
      unfold_phys_minmaxI H0.
      subst x. subst x0.
      rewrite <- HINST1 in HCUR. inv HCUR.
      rewrite HOP1 in HOP3. inv HOP3.
      unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET. des_ifs.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  constructor.
  hey_terminator2 HINST1 HTSTEP.
Qed.

(*****
      Refinement on getelementptr is not needed because
      physicalized_ptr already contains it. :)
      In the same context refinement on bitcast is also not
      needed because it returns identical value if
      the input is a pointer value.
 *****)

End GVN4.

End Ir.

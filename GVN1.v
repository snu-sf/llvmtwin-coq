Require Import Bool.
Require Import Sorting.Permutation.
Require Import Omega.
Require Import sflib.

Require Import Common.
Require Import Value.
Require Import Lang.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Refinement.
Require Import TwinExecution.

Module Ir.

Module GVN.

(**************************************************************
  This file proves validity of the first GVN optimization case:
 1. q is NULL or the result of an integer-to-pointer cast.

  High-level structure of proof is as follows:
  (1) We define the notion of `physicalized_ptr p1 p2`, meaning
      that p2 is derived from (int* )(int)p1.
      (Note that in GVN p2 will replace p1.)
  (2) We show that a function get_deref, which returns a
      dereferenced block (as well as offset), has some good
      relation on p1 and p2.
      To explain it briefly: if get_deref p1 succeeds,
      get_deref p2 also succeeds and returns the same result.
      The name of the lemma is physicalized_ptr_get_deref.
  (3) Using this, we can show that load/store/free holds
      refinement.
  (4) For other operations: using p2 instead of p1 makes
      the same result.
 **************************************************************)

Inductive physicalized_ptr: Ir.Memory.t -> Ir.val -> Ir.val -> Prop :=
| ps_base:
    forall m p1 p2
           (HP2:Some p2 = Ir.ptr_to_phy m p1),
      physicalized_ptr m (Ir.ptr p1) (Ir.ptr p2)
| ps_gep:
    forall m p1 p2 idx t inb p1' p2'
           (HBASE:physicalized_ptr m (Ir.ptr p1) (Ir.ptr p2))
           (HP1':p1' = Ir.SmallStep.gep p1 idx t m inb)
           (HP2':p2' = Ir.SmallStep.gep p2 idx t m inb),
      physicalized_ptr m p1' p2'.


Lemma physicalized_ptr_nonlog:
  forall m p1 p2
         (HPP:physicalized_ptr m (Ir.ptr p1) (Ir.ptr p2)),
    ~ exists l o, p2 = Ir.plog l o.
Proof.
  intros.
  remember (Ir.ptr p1) as v1.
  remember (Ir.ptr p2) as v2.
  generalize dependent p1.
  generalize dependent p2.
  induction HPP.
  { intros. inv Heqv1. inv Heqv2.
    unfold Ir.ptr_to_phy in HP2.
    destruct p3.
    { unfold Ir.log_to_phy in HP2.
      destruct (Ir.Memory.get m b).
      { intros HH. destruct HH. destruct H. rewrite H in HP2.
        congruence. }
      { congruence. }
    }
    { intros HH. destruct HH. destruct H. rewrite H in HP2.
      congruence. }
  }
  { intros. inv Heqv1. inv Heqv2.
    intros HH.
    destruct HH. destruct H0. rewrite H0 in H1.
    eapply IHHPP.
    reflexivity. reflexivity.
    unfold Ir.SmallStep.gep in H1.
    destruct p2.
    { destruct inb.
      { destruct (Ir.Memory.get m b) eqn:HGET.
        destruct (Ir.MemBlock.inbounds n t0 &&
         Ir.MemBlock.inbounds
           (Ir.SmallStep.twos_compl_add n (idx * Ir.ty_bytesz t) Ir.MEMSZ) t0)
                 eqn:HINB.
        eexists. eexists. reflexivity.
        eexists. eexists. reflexivity.
        eexists. eexists. reflexivity. }
      { eexists. eexists . reflexivity. }
    }
    { destruct inb.
      { des_ifs. }
      { congruence. }
    }
  }
Qed.

Lemma physicalized_ptr_phy:
  forall m o1 Is1 cid1 o2 Is2 cid2 v1 v2
         (HPP:physicalized_ptr m v1 v2)
         (HV1:v1 = Ir.ptr (Ir.pphy o1 Is1 cid1))
         (HV2:v2 = Ir.ptr (Ir.pphy o2 Is2 cid2)),
    o1 = o2 /\ lsubseq Is1 Is2 /\ cid2 = None.
Proof.
  intros.
  generalize dependent o1.
  generalize dependent Is1.
  generalize dependent cid1.
  generalize dependent o2.
  generalize dependent Is2.
  generalize dependent cid2.
  induction HPP.
  { intros.
    inv HV1.
    unfold Ir.ptr_to_phy in HP2. inv HP2.
    inv HV2.
    split. reflexivity.
    split. constructor.
    reflexivity.
  }
  { intros.
    destruct p2'; try congruence.
    destruct p1'; try congruence.
    inv HV2.
    inv HV1.
    destruct p2.
    { eapply physicalized_ptr_nonlog in HPP.
      exfalso. apply HPP. eexists. eexists. reflexivity.
    }
    { unfold Ir.SmallStep.gep in HP1'.
      
      destruct p1 eqn:HP;
      destruct inb eqn:HINB.
      destruct (Ir.Memory.get m b) eqn:HGET.
      destruct (Ir.MemBlock.inbounds n0 t0 &&
           Ir.MemBlock.inbounds
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t) Ir.PTRSZ) t0)
               eqn:HINB2.
      ss.
      ss.
      ss.
      congruence.
      destruct (idx * Ir.ty_bytesz t <? Nat.shiftl 1 (Ir.PTRSZ - 1)) eqn:HSHL.
      {
        destruct (n0 + idx * Ir.ty_bytesz t <? Ir.MEMSZ) eqn:HOFS.
        {
          inversion HP1'. subst o1. subst Is1. subst cid1.
          exploit IHHPP.
          { reflexivity. }
          { reflexivity. }
          intros HH. destruct HH. destruct H0.
          unfold Ir.SmallStep.gep in HP2'.
          rewrite HSHL in HP2'.
          destruct (n + idx * Ir.ty_bytesz t <? Ir.MEMSZ) eqn:HN.
          { inversion HP2'. subst n0. subst o. subst o2. subst Is2. subst cid2.
             split.
            { congruence. }
            split.
            { constructor. constructor. assumption. }
            { congruence. }
          }
          { ss. }
        }
        { ss. }
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        inversion HP1'. subst o o1 Is1 cid1.
        destruct HP1'.
        rewrite HSHL in HP2'.
        inversion HP2'. subst o2 Is2 cid2.
        destruct HP2'.
        split. congruence.
        split. constructor. constructor. assumption.
        congruence.
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        subst o.
        inversion HP2'. subst o2 Is2 cid2.
        destruct HP2'.
        inversion HP1'. subst o1 Is1 cid1.
        destruct HP1'.
        split. congruence. split. congruence. congruence.
      }
    }
  }
Qed.

Lemma PTRSZ_MEMSZ:
  Nat.shiftl 2 (Ir.PTRSZ - 1) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Lemma PTRSZ_MEMSZ2:
  Nat.double (Nat.shiftl 1 (Ir.PTRSZ - 1)) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Lemma MEMSZ_nonzero:
Ir.MEMSZ <> 0.
Proof.
  unfold Ir.MEMSZ.
  unfold Ir.PTRSZ.
  intros HH. simpl in HH.
  repeat (rewrite Nat.double_twice in HH).
  omega.
Qed.

Lemma inbounds_mod:
  forall mb (HWF:Ir.MemBlock.wf mb) ofs
         (HINB:Ir.MemBlock.inbounds ofs mb = true),
    (Ir.MemBlock.addr mb + ofs) mod Ir.MEMSZ = Ir.MemBlock.addr mb + ofs.
Proof.
  intros.
  rewrite Nat.mod_small. reflexivity.
  inv HWF.
  unfold Ir.MemBlock.inbounds in HINB.
  rewrite PeanoNat.Nat.leb_le in HINB.
  eapply Nat.le_lt_trans with (m := Ir.MemBlock.addr mb +Ir.MemBlock.n mb).
  omega.
  apply wf_inmem.
  unfold Ir.MemBlock.addr.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin. inv wf_twin.
  simpl. left. reflexivity.
Qed.

(* Thanks to twin blocks, size of a block cannot equal to or be larger than a half of
   memory size. *)
Lemma blocksz_lt:
  forall mb (HWF:Ir.MemBlock.wf mb),
    ~ (Ir.MemBlock.n mb >= Nat.shiftl 1 (Ir.PTRSZ - 1)).
Proof.
  intros.
  intros H.
  inv HWF.
  unfold Ir.MemBlock.P_ranges in wf_disj.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin. inv wf_twin.
  destruct l. simpl in wf_twin. inv wf_twin.
  simpl in wf_disj.
  rewrite andb_true_iff in wf_disj.
  rewrite andb_true_iff in wf_disj.
  rewrite andb_true_iff in wf_disj.
  destruct wf_disj.
  destruct H0. clear H1. clear H2.
  unfold disjoint_range in H0.
  rewrite orb_true_iff in H0.
  rewrite PeanoNat.Nat.leb_le in H0.
  rewrite PeanoNat.Nat.leb_le in H0.
  assert (Ir.MEMSZ = (Nat.shiftl 1 (Ir.PTRSZ - 1)) +
                     (Nat.shiftl 1 (Ir.PTRSZ - 1))).
  { reflexivity. }
  destruct H0.
  { exploit wf_inmem.
    simpl. right. left. reflexivity.
    intros HH.
    omega.
  }
  { exploit wf_inmem.
    simpl. left. reflexivity.
    intros HH. omega.
  }
Qed.  
  
Opaque Ir.MEMSZ.
Opaque Ir.PTRSZ.


Lemma physicalized_ptr_convert:
  forall m l1 o1 o2 Is2 cid2 v1 v2 mb
         (HPP:physicalized_ptr m v1 v2)
         (HV1:v1 = Ir.ptr (Ir.plog l1 o1))
         (HV2:v2 = Ir.ptr (Ir.pphy o2 Is2 cid2))
         (HGET:Some mb = Ir.Memory.get m l1),
    (Ir.MemBlock.addr mb + o1) mod Ir.MEMSZ = o2.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent o1.
  generalize dependent o2.
  generalize dependent Is2.
  generalize dependent cid2.
  generalize dependent mb.
  induction HPP.
  { intros.
    inv HV1.
    unfold Ir.ptr_to_phy in HP2. inv HP2.
    inv HV2.
    unfold Ir.log_to_phy in H0.
    rewrite <- HGET in H0.
    congruence.
  }
  { intros.
    destruct p2'; try congruence.
    destruct p1'; try congruence.
    inv HV2.
    inv HV1.
    destruct p2.
    { eapply physicalized_ptr_nonlog in HPP.
      exfalso. apply HPP. eexists. eexists. reflexivity.
    }
    { unfold Ir.SmallStep.gep in HP1'.
      destruct p1 eqn:HP.
      { (* log *)
        destruct inb eqn:HINB.
        { (* inbounds *)
          destruct (Ir.Memory.get m b) eqn:HGETB; try ss.
          exploit IHHPP.
          { reflexivity. }
          { reflexivity. }
          { rewrite HGETB. reflexivity. }
          intros HH.
          unfold Ir.SmallStep.gep in HP2'.
          destruct ((idx * (Ir.ty_bytesz t) <?
                     Nat.shiftl 1 (Ir.PTRSZ - 1))) eqn:H11.
          { (* positive offset add *)
            destruct (n + idx * Ir.ty_bytesz t <? Ir.MEMSZ) eqn:H2; try congruence.
            inversion HP2'. subst o2. subst Is2. subst cid2.
            rewrite PeanoNat.Nat.ltb_lt in H2.
            destruct (Ir.MemBlock.inbounds n0 t0 &&
                                           Ir.MemBlock.inbounds
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t) Ir.PTRSZ) t0)
                     eqn:HINB2.
            { inversion HP1'. subst l1. subst o1.
              unfold Ir.SmallStep.twos_compl_add.
              unfold Ir.SmallStep.twos_compl.
              rewrite PTRSZ_MEMSZ.
              rewrite Nat.add_mod_idemp_r.
              rewrite <- HH.
              rewrite Nat.add_mod_idemp_l.
              rewrite PeanoNat.Nat.add_assoc.
              rewrite HGETB in HGET. inv HGET. reflexivity.
              apply MEMSZ_nonzero. apply MEMSZ_nonzero.
            }
            { ss. }
          }
        { (* negaitve offset add *)
          destruct (Ir.MemBlock.inbounds n0 t0 &&
           Ir.MemBlock.inbounds
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t) Ir.PTRSZ) t0)
                   eqn:HINB2.
          {
            inv HP2'.
            inv HP1'.
            rewrite HGETB in HGET. inv HGET.
            unfold Ir.SmallStep.twos_compl_add.
            unfold Ir.SmallStep.twos_compl.
            rewrite PTRSZ_MEMSZ.
            rewrite Nat.add_mod_idemp_r.
            rewrite Nat.add_mod_idemp_l.
            rewrite PeanoNat.Nat.add_assoc. reflexivity.
            apply MEMSZ_nonzero. apply MEMSZ_nonzero.
          }
          { ss. }
        }
      }
      { (* no inbounds *)
        unfold Ir.SmallStep.gep in HP2'.
        inv HP2'.
        inv HP1'.
        exploit IHHPP;try reflexivity; try eassumption.
        intros HH. rewrite <- HH.
        unfold Ir.SmallStep.twos_compl_add.
        unfold Ir.SmallStep.twos_compl.
        rewrite PTRSZ_MEMSZ.
        rewrite Nat.add_mod_idemp_r.
        rewrite Nat.add_mod_idemp_l.
        rewrite PeanoNat.Nat.add_assoc. reflexivity.
        apply MEMSZ_nonzero. apply MEMSZ_nonzero.
      }
    }
    { des_ifs. }
    }
  }
Qed.


Ltac case1 := left; split; reflexivity.
Ltac case2 := right; left; split; [ reflexivity | eexists; reflexivity ].
Ltac case3 := right; right; split; [ eexists; reflexivity | eexists; reflexivity ].

Lemma physicalized_ptr_valty:
  forall m v1 v2
         (HWF:Ir.Memory.wf m)
         (HPP:physicalized_ptr m v1 v2),
    (v1 = Ir.poison /\ v2 = Ir.poison) \/
    (v1 = Ir.poison /\ exists p2, v2 = Ir.ptr p2) \/
    ((exists p1, v1 = Ir.ptr p1) /\ exists p2, v2 = Ir.ptr p2).
Proof.
  intros.
  generalize dependent HWF.
  induction HPP.
  { unfold Ir.ptr_to_phy in HP2.
    destruct p1.
    { unfold Ir.log_to_phy in HP2.
      destruct (Ir.Memory.get m b).
      { right. right. split. eexists. reflexivity.
        exists (Ir.pphy ((Ir.MemBlock.addr t + n) mod Ir.MEMSZ) [] None).
        congruence. }
      congruence.
    }
    { inv HP2. case3. }
  }
  { intros.
    destruct IHHPP.
    { assumption. }
    { destruct H. congruence. }
    destruct H.
    { destruct H. congruence. }
    destruct H.
    destruct H. destruct H0.
    inversion H. subst x. inversion H0. subst x0.
    (* p2 is never logical. *)
    destruct p2.
    eapply physicalized_ptr_nonlog in HPP. exfalso. apply HPP.
      eexists. eexists. reflexivity.
    unfold Ir.SmallStep.gep in HP2'.
    unfold Ir.SmallStep.gep in HP1'.
    des_ifs; try case1; try case2; try case3.
    { eapply physicalized_ptr_convert in HPP; try reflexivity.
      2: rewrite Heq. 2: reflexivity.
      rename n0 into ofs.
      rename n into absofs.
      remember (idx * Ir.ty_bytesz t) as d.
      subst absofs.
      rewrite PeanoNat.Nat.ltb_nlt in Heq2.
      rewrite PeanoNat.Nat.ltb_lt in Heq1.
      rewrite andb_true_iff in Heq0.
      destruct Heq0.
      unfold Ir.MemBlock.inbounds in H2.
      unfold Ir.SmallStep.twos_compl_add in H2.
      unfold Ir.SmallStep.twos_compl in H2.
      rewrite PTRSZ_MEMSZ in H2.
      rewrite inbounds_mod in Heq2; try assumption.
      rewrite PeanoNat.Nat.leb_le in H2.
      apply not_lt in Heq2.
      unfold Ir.MemBlock.inbounds in H1.
      rewrite PeanoNat.Nat.leb_le in H1.
      assert (Ir.MemBlock.n t0 < Nat.shiftl 1 (Ir.PTRSZ - 1)).
      { inv HWF.
        assert (Ir.MemBlock.wf t0).
        { eapply wf_blocks.
          symmetry in Heq.
          eapply Ir.Memory.get_In in Heq. eassumption.
          reflexivity. }
        assert (HH := blocksz_lt t0 H3).
        apply not_ge in HH.
        assumption. }
      rewrite Nat.mod_small in H2.
      assert (Ir.MemBlock.addr t0 + Ir.MemBlock.n t0 < Ir.MEMSZ).
      { inv HWF.
        exploit wf_blocks. symmetry in Heq.
        eapply Ir.Memory.get_In in Heq. eassumption. reflexivity.
        intros HH.
        inv HH.
        eapply wf_inmem.
        unfold Ir.MemBlock.addr.
        destruct (Ir.MemBlock.P t0). 
        simpl in wf_twin. inv wf_twin. simpl. intuition. }
      rewrite <- PTRSZ_MEMSZ2 in Heq2, H4.
      unfold Nat.double in *. omega.
      rewrite <- PTRSZ_MEMSZ2. unfold Nat.double. omega.
      inv HWF. eapply wf_blocks.
      eapply Ir.Memory.get_In. rewrite Heq. reflexivity. reflexivity.
    }
    { eapply physicalized_ptr_phy in HPP; try reflexivity.
      destruct HPP. destruct H2. subst n0. subst o.
      congruence.
    }
  }
Qed.
      

Lemma eq_incrpc2:
  forall md1 md2 st i1 i2
      (HINST1: Some i1 = Ir.Config.cur_inst md1 st)
      (HINST2: Some i2 = Ir.Config.cur_inst md2 st),
    Ir.Config.eq (Ir.SmallStep.incrpc md1 st) (Ir.SmallStep.incrpc md2 st).
Proof.
  intros.
  unfold Ir.Config.cur_inst in HINST1.
  unfold Ir.Config.cur_inst in HINST2.
  split.
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      repeat (rewrite Ir.Config.m_update_pc);
      unfold Ir.Config.update_rval; des_ifs.
  }
  split.
  { unfold Ir.Config.cur_fdef_pc in HINST1.
    unfold Ir.Config.cur_fdef_pc in HINST2.
    des_ifs.
    unfold Ir.IRFunction.get_inst in HINST1.
    unfold Ir.IRFunction.get_inst in HINST2.
    destruct p1; try congruence.
    des_ifs.
    unfold Ir.SmallStep.incrpc.
    unfold Ir.Config.cur_fdef_pc.
    rewrite Heq0.
    rewrite Heq1.
    rewrite Heq2.
    rewrite Heq3.
    unfold Ir.IRFunction.next_trivial_pc.
    rewrite Heq5.
    rewrite Heq.
    rewrite Heq6.
    rewrite Heq4.
    apply Ir.Stack.eq_refl.
  }
  split.
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; des_ifs.
  }
  { unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; des_ifs.
  }
Qed.

Lemma eq_update_reg_and_incrpc2:
  forall md1 md2 st r v i1 i2
      (HINST1: Some i1 = Ir.Config.cur_inst md1 st)
      (HINST2: Some i2 = Ir.Config.cur_inst md2 st),
    Ir.Config.eq
      (Ir.SmallStep.update_reg_and_incrpc md1 st r v)
      (Ir.SmallStep.update_reg_and_incrpc md2 st r v).
Proof.
  intros.
  unfold Ir.Config.cur_inst in HINST1.
  unfold Ir.Config.cur_inst in HINST2.
  split.
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      repeat (rewrite Ir.Config.m_update_pc);
      unfold Ir.Config.update_rval; des_ifs.
  }
  split.
  { unfold Ir.Config.cur_fdef_pc in HINST1.
    unfold Ir.Config.cur_fdef_pc in HINST2.
    des_ifs.
    unfold Ir.IRFunction.get_inst in HINST1.
    unfold Ir.IRFunction.get_inst in HINST2.
    destruct p1; try congruence.
    des_ifs.
    unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    rewrite Ir.Config.cur_fdef_pc_update_rval.
    rewrite Ir.Config.cur_fdef_pc_update_rval.
    unfold Ir.Config.cur_fdef_pc.
    rewrite Heq0.
    rewrite Heq1.
    rewrite Heq2.
    rewrite Heq3.
    unfold Ir.IRFunction.next_trivial_pc.
    rewrite Heq5.
    rewrite Heq.
    rewrite Heq6.
    rewrite Heq4.
    apply Ir.Stack.eq_refl.
  }
  split.
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; unfold Ir.Config.update_rval;
      des_ifs.
  }
  { unfold Ir.SmallStep.update_reg_and_incrpc.
    unfold Ir.SmallStep.incrpc.
    des_ifs;
      unfold Ir.Config.update_pc; unfold Ir.Config.update_rval;
      des_ifs.
  }
Qed.



Lemma inbounds_added_abs_true:
  forall m b t0 n0 n ofs
    (wf_m:Ir.Memory.wf m)
    (HGET:Ir.Memory.get m b = Some t0)
    (HPP:(Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ = n)
    (HINB:Ir.MemBlock.inbounds
         (Ir.SmallStep.twos_compl_add n0 ofs Ir.PTRSZ) t0 = true),
  Ir.MemBlock.inbounds_abs
                      ((n + ofs) mod Ir.MEMSZ) t0 = true.
Proof.
  intros.
  erewrite Ir.MemBlock.inbounds_inbounds_abs in HINB; try reflexivity.
  rewrite <- HPP.
  assert ((Ir.SmallStep.twos_compl_add n0 ofs Ir.PTRSZ
           + Ir.MemBlock.addr t0) =
          ((Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ + ofs)
            mod Ir.MEMSZ).
  { unfold Ir.SmallStep.twos_compl_add.
    unfold Ir.SmallStep.twos_compl.
    rewrite PTRSZ_MEMSZ.
    rewrite Nat.add_mod_idemp_l.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc with (n := Ir.MemBlock.addr t0).
    rewrite <- Nat.add_mod_idemp_r with (b := (n0 + ofs)).
    rewrite Nat.mod_small with
        (a := (Ir.MemBlock.addr t0 + (n0 + ofs)
                                       mod Ir.MEMSZ)).
    reflexivity.
    { (* Ir.MemBlock.addr t0 + (n0 + idx * Ir.ty_bytesz t)
         mod Ir.MEMSZ < Ir.MEMSZ *)
      unfold Ir.MemBlock.inbounds_abs in HINB.
      unfold in_range in HINB.
      rewrite andb_true_iff in HINB.
      destruct HINB.
      rewrite PeanoNat.Nat.leb_le in H0, H.
      unfold Ir.SmallStep.twos_compl_add in H0.
      unfold Ir.SmallStep.twos_compl in H0.
      rewrite PTRSZ_MEMSZ in H0.
      rewrite Nat.add_comm with (m := Ir.MemBlock.addr t0) in H0.
      assert (fst (Ir.MemBlock.P0_range t0) + snd (Ir.MemBlock.P0_range t0)
              < Ir.MEMSZ).
      { unfold Ir.MemBlock.P0_range.
        simpl.
        destruct wf_m.
        symmetry in HGET.
        eapply Ir.Memory.get_In in HGET;try reflexivity.
        apply wf_blocks in HGET.
        destruct HGET.
        apply wf_inmem.
        unfold Ir.MemBlock.addr.
        destruct (Ir.MemBlock.P t0).
        { simpl in wf_twin. unfold Ir.TWINCNT in wf_twin. congruence. }
        { simpl. left. reflexivity. }
      }
      eapply Nat.le_lt_trans.
      eapply H0.
      eassumption.
    }
    apply MEMSZ_nonzero.
    apply MEMSZ_nonzero.
  }
  rewrite H in HINB.
  assumption.
Qed.

Lemma inbounds_abs_true:
  forall m b t0 n0 n
    (wf_m:Ir.Memory.wf m)
    (HGET:Ir.Memory.get m b = Some t0)
    (HPP:(Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ = n)
    (HINB:Ir.MemBlock.inbounds n0 t0 = true),
  Ir.MemBlock.inbounds_abs n t0 = true.
Proof.
  intros.
  erewrite Ir.MemBlock.inbounds_inbounds_abs in HINB;
    try reflexivity.
  rewrite <- HPP.
  assert ((Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ =
          n0 + Ir.MemBlock.addr t0).
  { unfold Ir.MemBlock.inbounds_abs in HINB.
    unfold in_range in HINB.
    rewrite andb_true_iff in HINB.
    destruct HINB.
    rewrite Nat.leb_le in H0.
    unfold Ir.MemBlock.P0_range in H0.
    simpl in H0.
    inv wf_m.
    symmetry in HGET.
    eapply Ir.Memory.get_In in HGET; try reflexivity.
    apply wf_blocks in HGET.
    inv HGET.
    rewrite Nat.mod_small.
    omega.
    eapply Nat.le_lt_trans.
    rewrite Nat.add_comm.
    eassumption.
    eapply wf_inmem.
    unfold Ir.MemBlock.addr.
    destruct (Ir.MemBlock.P t0).
    { simpl in wf_twin. unfold Ir.TWINCNT in wf_twin. omega. }
    { simpl. eauto. }
  }
  rewrite H. assumption.
Qed.

Lemma inbounds_added_abs_true2:
  forall m b t0 n0 n ofs sz
    (wf_m:Ir.Memory.wf m)
    (HGET:Ir.Memory.get m b = Some t0)
    (HPP:(Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ = n)
    (HINB:Ir.MemBlock.inbounds
         (Ir.SmallStep.twos_compl_add n0 ofs Ir.PTRSZ + sz) t0 = true),
  Ir.MemBlock.inbounds_abs
                      ((n + ofs) mod Ir.MEMSZ + sz) t0 = true.
Proof.
  intros.
  erewrite Ir.MemBlock.inbounds_inbounds_abs in HINB; try reflexivity.
  rewrite <- HPP.
  assert ((Ir.SmallStep.twos_compl_add n0 ofs Ir.PTRSZ
           + Ir.MemBlock.addr t0) =
          ((Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ + ofs)
            mod Ir.MEMSZ).
  { unfold Ir.SmallStep.twos_compl_add.
    unfold Ir.SmallStep.twos_compl.
    rewrite PTRSZ_MEMSZ.
    rewrite Nat.add_mod_idemp_l.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc with (n := Ir.MemBlock.addr t0).
    rewrite <- Nat.add_mod_idemp_r with (b := (n0 + ofs)).
    rewrite Nat.mod_small with
        (a := (Ir.MemBlock.addr t0 + (n0 + ofs)
                                       mod Ir.MEMSZ)).
    reflexivity.
    { (* Ir.MemBlock.addr t0 + (n0 + idx * Ir.ty_bytesz t)
         mod Ir.MEMSZ < Ir.MEMSZ *)
      unfold Ir.MemBlock.inbounds_abs in HINB.
      unfold in_range in HINB.
      rewrite andb_true_iff in HINB.
      destruct HINB.
      rewrite PeanoNat.Nat.leb_le in H0, H.
      unfold Ir.SmallStep.twos_compl_add in H0.
      unfold Ir.SmallStep.twos_compl in H0.
      rewrite PTRSZ_MEMSZ in H0.
      rewrite Nat.add_comm with (m := Ir.MemBlock.addr t0) in H0.
      assert (fst (Ir.MemBlock.P0_range t0) + snd (Ir.MemBlock.P0_range t0)
              < Ir.MEMSZ).
      { unfold Ir.MemBlock.P0_range.
        simpl.
        destruct wf_m.
        symmetry in HGET.
        eapply Ir.Memory.get_In in HGET;try reflexivity.
        apply wf_blocks in HGET.
        destruct HGET.
        apply wf_inmem.
        unfold Ir.MemBlock.addr.
        destruct (Ir.MemBlock.P t0).
        { simpl in wf_twin. unfold Ir.TWINCNT in wf_twin. congruence. }
        { simpl. left. reflexivity. }
      }
      eapply Nat.le_lt_trans.
      eapply Nat.le_trans with (m := Ir.MemBlock.addr t0 + ((n0 + ofs) mod Ir.MEMSZ + sz)).
      omega.
      eapply H0.
      eassumption.
    }
    apply MEMSZ_nonzero.
    apply MEMSZ_nonzero.
  }
  rewrite <- Nat.add_assoc in HINB.
  rewrite Nat.add_comm with (n := sz) in HINB.
  rewrite Nat.add_assoc in HINB.
  rewrite H in HINB.
  assumption.
Qed.

Lemma inbounds_abs_true2:
  forall m b t0 n0 n sz
    (wf_m:Ir.Memory.wf m)
    (HGET:Ir.Memory.get m b = Some t0)
    (HPP:(Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ = n)
    (HINB:Ir.MemBlock.inbounds (n0 + sz) t0 = true),
  Ir.MemBlock.inbounds_abs (n + sz) t0 = true.
Proof.
  intros.
  erewrite Ir.MemBlock.inbounds_inbounds_abs in HINB;
    try reflexivity.
  rewrite <- HPP.
  assert ((Ir.MemBlock.addr t0 + n0) mod Ir.MEMSZ =
          n0 + Ir.MemBlock.addr t0).
  { unfold Ir.MemBlock.inbounds_abs in HINB.
    unfold in_range in HINB.
    rewrite andb_true_iff in HINB.
    destruct HINB.
    rewrite Nat.leb_le in H0.
    unfold Ir.MemBlock.P0_range in H0.
    simpl in H0.
    inv wf_m.
    symmetry in HGET.
    eapply Ir.Memory.get_In in HGET; try reflexivity.
    apply wf_blocks in HGET.
    inv HGET.
    rewrite Nat.mod_small.
    omega.
    eapply Nat.le_lt_trans.
    rewrite Nat.add_comm.
    eapply Nat.le_trans with (m := n0 + sz + Ir.MemBlock.addr t0).
    omega.
    eassumption.
    eapply wf_inmem.
    unfold Ir.MemBlock.addr.
    destruct (Ir.MemBlock.P t0).
    { simpl in wf_twin. unfold Ir.TWINCNT in wf_twin. omega. }
    { simpl. eauto. }
  }
  rewrite H.
  rewrite <- Nat.add_assoc.
  rewrite Nat.add_comm with (m := sz).
  rewrite Nat.add_assoc.
  assumption.
Qed.

Lemma inbounds_tcadd_abs:
  forall m b t0 ofs n n0
    (wf_m:Ir.Memory.wf m)
    (HGET:Ir.Memory.get m b = Some t0)
    (HINB:Ir.MemBlock.inbounds
            (Ir.SmallStep.twos_compl_add n ofs Ir.PTRSZ) t0 = true)
    (HPP:(Ir.MemBlock.addr t0 + n) mod Ir.MEMSZ = n0),
  Ir.MemBlock.inbounds_abs
      (Ir.SmallStep.twos_compl_add n0 ofs Ir.PTRSZ) t0 = true.
Proof.
  intros.
  unfold Ir.SmallStep.twos_compl_add.
  unfold Ir.SmallStep.twos_compl.
  eapply inbounds_added_abs_true; try eassumption.
Qed.

Lemma physicalized_ptr_log_I:
  forall v1 v2 m
         (HPP:physicalized_ptr m v1 v2),
    forall md l1 o1 o2 I2 cid2 mb st
         (HM:m = Ir.Config.m st)
         (HWF:Ir.Config.wf md st)
         (HV1:v1 = Ir.ptr (Ir.plog l1 o1))
         (HV2:v2 = Ir.ptr (Ir.pphy o2 I2 cid2))
         (HGET:Some mb = Ir.Memory.get (Ir.Config.m st) l1),
    List.forallb (fun i => Ir.MemBlock.inbounds_abs i mb) I2 = true.
Proof.
  intros v1 v2 st HPP.
  induction HPP.
  { intros.
    unfold Ir.ptr_to_phy in HP2.
    destruct p1.
    { unfold Ir.log_to_phy in HP2.
      inv HV1.
      rewrite <- HGET in HP2.
      inv HP2.
      inv HV2. reflexivity. }
    { inv HP2. inv HV2. reflexivity. }
  }
  { intros.
    inv HV1.
    inv HV2.
    unfold Ir.SmallStep.gep in H.
    des_ifs.
    { unfold Ir.SmallStep.gep in H1.
      des_ifs.
      { rewrite Heq in HGET. inv HGET. symmetry in Heq.
        simpl.
        dup HWF. inv HWF.
        eapply physicalized_ptr_convert in HPP; try eassumption; try reflexivity.
        rewrite andb_true_iff in Heq0.
        destruct Heq0.
        rewrite <- HPP.
        symmetry in Heq.
        erewrite inbounds_abs_true with (n0 := n); try eassumption; try reflexivity.
        erewrite inbounds_tcadd_abs; try eassumption; try reflexivity.
        erewrite IHHPP; try reflexivity; try eassumption.
        congruence.
      }
      { rewrite Heq in HGET. inv HGET. symmetry in Heq.
        simpl.
        dup HWF. inv HWF.
        eapply physicalized_ptr_convert in HPP; try eassumption; try reflexivity.
        rewrite andb_true_iff in Heq0.
        destruct Heq0.
        rewrite <- HPP.
        symmetry in Heq.
        erewrite inbounds_abs_true with (n0 := n); try eassumption; try reflexivity.
        erewrite inbounds_tcadd_abs; try eassumption; try reflexivity.
        erewrite IHHPP; try reflexivity; try eassumption.
        congruence.
      }
    }
    { unfold Ir.SmallStep.gep in H1.
      des_ifs.
      erewrite IHHPP; try reflexivity; try eassumption.
    }
  }
Qed.

(* NOTE: This lemma does not hold anymore if function call is introduced.
 This lemma should be replaced with something else which gives criteria
 to cid. (ex: cid is never bogus) *)
Lemma physicalized_ptr_log_cid:
  forall v1 v2 m
         (HPP:physicalized_ptr m v1 v2),
    forall md l1 o1 o2 I2 cid2 mb st
         (HM:m = Ir.Config.m st)
         (HWF:Ir.Config.wf md st)
         (HV1:v1 = Ir.ptr (Ir.plog l1 o1))
         (HV2:v2 = Ir.ptr (Ir.pphy o2 I2 cid2))
         (HGET:Some mb = Ir.Memory.get (Ir.Config.m st) l1),
      cid2 = None.
Proof.
  intros v1 v2 m HPP.
  induction HPP.
  { intros. inv HV1. inv HV2. unfold Ir.ptr_to_phy in HP2.
    unfold Ir.log_to_phy in HP2.
    des_ifs.
  }
  { intros. inv HV1. inv HV2.
    unfold Ir.SmallStep.gep in *.
    des_ifs.
    { eapply IHHPP.
      reflexivity. eassumption. reflexivity. reflexivity. eassumption. }
    { eapply IHHPP.
      reflexivity. eassumption. reflexivity. reflexivity. eassumption. }
    { eapply IHHPP.
      reflexivity. eassumption. reflexivity. reflexivity. eassumption. }
  }
Qed.

Lemma physicalized_ptr_log_get:
  forall v1 v2 m
         (HPP:physicalized_ptr m v1 v2),
    forall md l1 o1 st
         (HM:m = Ir.Config.m st)
         (HWF:Ir.Config.wf md st)
         (HV1:v1 = Ir.ptr (Ir.plog l1 o1)),
      exists mb, Some mb = Ir.Memory.get (Ir.Config.m st) l1.
Proof.
  intros v1 v2 m HPP.
  induction HPP.
  { intros. inv HV1. unfold Ir.ptr_to_phy in HP2.
    unfold Ir.log_to_phy in HP2.
    des_ifs. eexists. reflexivity.
  }
  { intros. inv HV1.
    unfold Ir.SmallStep.gep in *.
    des_ifs.
    { eapply IHHPP.
      reflexivity. eassumption. reflexivity. }
    { eapply IHHPP.
      reflexivity. eassumption. reflexivity. }
  }
Qed.

Lemma physicalized_ptr_get_deref:
  forall md st sz p1 p2
         (HWF:Ir.Config.wf md st)
         (HSZ:sz> 0)
         (HPP:physicalized_ptr (Ir.Config.m st) (Ir.ptr p1) (Ir.ptr p2)),
    (exists blk, Ir.get_deref (Ir.Config.m st) p1 sz = [blk] /\
                 Ir.get_deref (Ir.Config.m st) p2 sz = [blk]) \/
    (Ir.get_deref (Ir.Config.m st) p1 sz = []).
Proof.
  intros.
  destruct p2.
  { (* p2 is never log -> no *)
    eapply physicalized_ptr_nonlog in HPP.
    exfalso. eapply HPP. eauto. }
  destruct p1.
  { (* p1 is log! *)
    dup HPP.
    dup HPP.
    dup HPP.
    eapply physicalized_ptr_log_get in HPP; try reflexivity; try eassumption.
    destruct HPP.
    eapply physicalized_ptr_convert in HPP0; try reflexivity; try eassumption.
    eapply physicalized_ptr_log_I in HPP1; try reflexivity; try eassumption.
    eapply physicalized_ptr_log_cid in HPP2; try reflexivity; try eassumption.
    remember (Ir.get_deref (Ir.Config.m st) (Ir.plog b n0) sz) as res.
    dup Heqres.
    symmetry in Heqres.
    eapply Ir.get_deref_log in Heqres.
    2: rewrite <- H. 2: reflexivity.
    destruct Heqres.
    { (* okay, deref p1 succeeded. *)
      subst res.
      (* b is alive. *)
      dup H0.
      eapply Ir.get_deref_log_alive in H1; try eassumption.
      left. eexists.
      split. eassumption.
      subst o.
      (* prepare to apply get_deref_ptr_phy_same. *)
      remember (Ir.ptr_to_phy (Ir.Config.m st) (Ir.plog b n0)).
      symmetry in Heqo. dup Heqo.
      unfold Ir.ptr_to_phy in Heqo.
      unfold Ir.log_to_phy in Heqo.
      rewrite <- H in Heqo.
      rewrite HPP0 in Heqo.
      rewrite <- Heqo in Heqo0. clear Heqo.
      eapply Ir.get_deref_ptr_phy_same
        with (p' := Ir.pphy n [] None) in H0; try assumption.
      (* time to promote get_deref (pphy n [] None) into
         get_deref (pphy n l None). *)
      eapply Ir.get_deref_phy_I3; try assumption.
      (* well, memory wf.. *)
      inv HWF. assumption.
      inv HWF. assumption.
    }
    { (* Oh, deref p1 failed. *)
      intuition.
    }
  }
  { (* p1 is phy. *)
    dup HPP.
    eapply physicalized_ptr_phy in HPP0; try reflexivity.
    inv HPP0. inv H0.
    (* same here. let's use Ir.get_deref_ptr_phy_same:
       Ir.get_deref m p sz = [bo] ->
       Ir.ptr_to_phy m p = Some p' -> Ir.get_deref m p' sz = [bo]. *)
    remember (Ir.get_deref (Ir.Config.m st) (Ir.pphy n l0 o0) sz) as res.
    dup Heqres.
    symmetry in Heqres0.
    eapply Ir.get_deref_phy_singleton in Heqres0; try omega.
    destruct Heqres0.
    { (* succeeded. *)
      destruct H0.
      destruct H0.
      inv H0. destruct H1. destruct x. destruct p. simpl in H0.
      simpl in H1.
      (* make cid *)
      eapply Ir.get_deref_phy_cid3 in H2; try congruence.
      left. eexists. split. reflexivity.
      eapply Ir.get_deref_phy_I_subseq; try eassumption.
      congruence.
      (* well, memory wf.. *)
      inv HWF. assumption.
      inv HWF. assumption.
    }
    { (* failed. *)
      intuition.
    }
    inv HWF. assumption.
  }
Qed.

Lemma load_val_get_deref:
  forall m ptr1 ptr2 retty
         (HEQ:Ir.get_deref m ptr1 (Ir.ty_bytesz retty) =
              Ir.get_deref m ptr2 (Ir.ty_bytesz retty)),
    Ir.load_val m ptr1 retty = Ir.load_val m ptr2 retty.
Proof.
  intros.
  unfold Ir.load_val.
  unfold Ir.load_bytes.
  rewrite HEQ.
  reflexivity.
Qed.


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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
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
      clear wf_no_bogus_ptr.
      clear wf_no_bogus_ptr_mem.

      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP.
      { (* poison, poison *)
        inv H. inv HNEXT. inv HNEXT0. constructor. }
      destruct H.
      { (* poison, ptr *)
        inv H. destruct H1. inv HNEXT.
        constructor. }
      { (* ptr, ptr *)
        inv H. inv H0. inv H1.
        eapply physicalized_ptr_get_deref with
          (sz := Ir.ty_bytesz retty) in HPP0; try eassumption.
        destruct HPP0.
        { inv H. inv H0.
          unfold Ir.deref in *.
          rewrite H in HNEXT. rewrite H1 in HNEXT0.
          inv HNEXT. inv HNEXT0.
          constructor. constructor.
          erewrite load_val_get_deref with (ptr2 := x);
            try congruence.
          eapply eq_update_reg_and_incrpc2; eassumption.
        }
        { (* src fails *)
          unfold Ir.deref in *.
          rewrite H in HNEXT. inv HNEXT. constructor.
        }
        apply Ir.ty_bytesz_pos.
      }
      inv HWF2. assumption.
    }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      congruence. }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      unfold Ir.SmallStep.t_step in HTSTEP.
      des_ifs. }
  }
  { constructor. }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
    unfold Ir.SmallStep.t_step in HTSTEP.
    des_ifs. }
Qed.


Lemma store_val_get_deref:
  forall m ptr1 ptr2 v valty
         (HEQ:Ir.get_deref m ptr1 (Ir.ty_bytesz valty) =
              Ir.get_deref m ptr2 (Ir.ty_bytesz valty)),
    Ir.store_val m ptr1 v valty = Ir.store_val m ptr2 v valty.
Proof.
  intros.
  unfold Ir.store_val.
  unfold Ir.store_bytes.
  destruct valty; destruct v; try reflexivity.
  {
    destruct (Ir.ty_bytesz (Ir.ity n) =? length (Ir.Byte.ofint
                                                 (BinNatDef.N.of_nat n0) n))
    eqn:HH;
      try reflexivity.
    rewrite PeanoNat.Nat.eqb_eq in HH.
    rewrite HH in *.
    rewrite HEQ. reflexivity. }
  {
    destruct (Ir.ty_bytesz (Ir.ptrty valty) =? length (Ir.Byte.ofptr p)) eqn:HH;
      try reflexivity.
    rewrite PeanoNat.Nat.eqb_eq in HH.
    rewrite HH in *.
    rewrite HEQ. reflexivity. }
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
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
      clear wf_no_bogus_ptr.
      clear wf_no_bogus_ptr_mem.

      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP.
      { (* poison, poison *)
        inv H. inv HNEXT. inv HNEXT0.
        des_ifs; try constructor. constructor.
        eapply eq_incrpc2; eassumption.
      }
      destruct H.
      { (* poison, ptr *)
        inv H. destruct H1. inv HNEXT.
        des_ifs; try constructor. constructor.
        eapply eq_incrpc2; eassumption. }
      { (* ptr, ptr *)
        inv H. inv H0. inv H1.
        eapply physicalized_ptr_get_deref with
          (sz := Ir.ty_bytesz valty) in HPP0; try eassumption.
        destruct HPP0.
        { inv H. inv H0.
          unfold Ir.deref in *.
          rewrite H in HNEXT. rewrite H1 in HNEXT0.
          inv HNEXT. inv HNEXT0.
          des_ifs; try constructor.
          constructor.
          erewrite store_val_get_deref with (ptr2 := x);
            try congruence.
          eapply eq_incrpc2; eassumption.
          constructor.
          eapply eq_incrpc2; eassumption.
        }
        { (* src fails *)
          unfold Ir.deref in *.
          rewrite H in HNEXT.
          des_ifs; try constructor.
          constructor.
          eapply eq_incrpc2; eassumption.
        }
        apply Ir.ty_bytesz_pos.
      }
      inv HWF2. assumption.
    }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      congruence. }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      unfold Ir.SmallStep.t_step in HTSTEP.
      des_ifs. }
  }
  { constructor. }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
    unfold Ir.SmallStep.t_step in HTSTEP.
    des_ifs. }
Qed.


Lemma n_pos:
  forall mb (HWF:Ir.MemBlock.wf mb),
    Ir.MemBlock.n mb > 0.
Proof.
  intros.
  inv HWF.
  unfold Ir.MemBlock.P_ranges in wf_poslen.
  unfold no_empty_range in wf_poslen.
  destruct (Ir.MemBlock.P mb).
  simpl in wf_twin. inv wf_twin.
  simpl in wf_poslen.
  rewrite andb_true_iff in wf_poslen.
  destruct wf_poslen. rewrite PeanoNat.Nat.ltb_lt in H.
  omega.
Qed.

Lemma zeroofs_block_addr:
  forall mb bid m (HGET:Ir.Memory.get m bid = Some mb)
         (HWF:Ir.Memory.wf m)
         (HALIVE:Ir.MemBlock.alive mb = true),
    Ir.Memory.zeroofs_block m (Ir.MemBlock.addr mb) = Some (bid, mb).
Proof.
  intros.
  unfold Ir.Memory.zeroofs_block.
  remember (Ir.Memory.inbounds_blocks2 m
    [Ir.MemBlock.addr mb; Ir.MemBlock.addr mb + 1]) as blks.
  symmetry in Heqblks.
  dup Heqblks.
  assert (List.In (bid, mb) blks).
  { rewrite <- Heqblks0.
    eapply Ir.Memory.inbounds_blocks2_In3.
    congruence. omega.
    unfold Ir.MemBlock.inbounds_abs.
    rewrite andb_true_iff.
    unfold in_range.
    unfold Ir.MemBlock.P0_range.
    simpl.
    rewrite Nat.leb_refl.
    assert (1 <= Ir.MemBlock.n mb).
    { eapply n_pos. inv HWF.
      exploit wf_blocks.
      symmetry in HGET.
      eapply Ir.Memory.get_In in HGET. eassumption. reflexivity.
      eauto. }
    simpl.
    repeat (rewrite andb_true_iff).
    repeat (rewrite PeanoNat.Nat.leb_le).
    omega.
    assumption.
  }
  eapply Ir.Memory.inbounds_blocks2_singleton in Heqblks.
  destruct blks. inv H.
  destruct blks.
  inv H. simpl. rewrite PeanoNat.Nat.eqb_refl. reflexivity.
  inv H0. simpl in Heqblks. omega.
  assumption.
  omega.
Qed.

Lemma free_get_deref:
  forall m (HWF:Ir.Memory.wf m)
         ptr bid blk (HDEREF:Ir.get_deref m ptr 1 = [(bid, blk, 0)]),
    Ir.SmallStep.free ptr m = Ir.Memory.free m bid.
Proof.
  intros.
  unfold Ir.SmallStep.free.
  destruct ptr.
  { dup HDEREF.
    unfold Ir.get_deref in HDEREF0.
    des_ifs. }
  { dup HDEREF.
    eapply Ir.get_deref_phy_singleton in HDEREF0; try omega; try assumption.
    inv HDEREF0; try congruence.
    inv H. inv H0. inv H1.
    destruct x. destruct p. inv H.
    simpl in H0.
    rewrite Nat.add_0_r in *.
    unfold Ir.deref.
    rewrite HDEREF.
    simpl.
    erewrite zeroofs_block_addr. reflexivity.
    assumption. assumption.
    SearchAbout Ir.get_deref.
    eapply Ir.get_deref_inv in HDEREF.
    rewrite andb_true_iff in HDEREF. destruct HDEREF.
    rewrite andb_true_iff in H. destruct H. assumption.
    omega.
    assumption. assumption.
  }
Qed.

Lemma free_get_deref2:
  forall m (HWF:Ir.Memory.wf m) n
         ptr bid blk (HDEREF:Ir.get_deref m ptr 1 = [(bid, blk, S n)]),
    Ir.SmallStep.free ptr m = None.
Proof.
  intros.
  unfold Ir.SmallStep.free.
  destruct ptr; try reflexivity.
  { eapply Ir.get_deref_log with (blk := blk) in HDEREF.
    inv HDEREF. inv H. reflexivity.
    inv H.
    unfold Ir.get_deref in HDEREF. des_ifs.
  }
  { unfold Ir.Memory.zeroofs_block.
    dup HDEREF.
    eapply Ir.get_deref_inv in HDEREF; try assumption; try omega.
    { rewrite andb_true_iff in HDEREF.
      rewrite andb_true_iff in HDEREF.
      destruct HDEREF. destruct H.
      eapply Ir.get_deref_phy_singleton in HDEREF0; try assumption; try omega.
      inv HDEREF0; try ss. inv H2. inv H3. inv H2.
      simpl in H4. inv H4.
      erewrite Ir.MemBlock.inbounds_inbounds_abs in H1; try reflexivity.
      erewrite Ir.MemBlock.inbounds_inbounds_abs in H0; try reflexivity.
      assert (Ir.Memory.inbounds_blocks2 m
           [Ir.MemBlock.addr blk + S n; Ir.MemBlock.addr blk + S n + 1]
              = [(bid, blk)]).
      { eapply Ir.Memory.inbounds_blocks2_singleton3.
        assumption.
        congruence.
        assumption.
        omega.
        rewrite Nat.add_comm. assumption.
        simpl in H0. rewrite Nat.add_comm with (m := S n).
        simpl. rewrite Nat.add_shuffle0. assumption.
      }
      rewrite H3. simpl.
      assert ((Ir.MemBlock.addr blk =? Ir.MemBlock.addr blk + S n) = false).
      { rewrite PeanoNat.Nat.eqb_neq. omega. }
      rewrite H4. reflexivity.
    }
    {
      eapply Ir.get_deref_phy_singleton in HDEREF0; try assumption; try omega.
      inv HDEREF0. inv H. inv H0. inv H1. inv H.
      simpl in H0. congruence. congruence. }
  }
Qed.

Lemma free_get_deref3:
  forall m (HWF:Ir.Memory.wf m)
         ptr (HDEREF:Ir.get_deref m ptr 1 = []),
    Ir.SmallStep.free ptr m = None.
Proof.
  intros.
  unfold Ir.SmallStep.free.
  destruct ptr.
  { dup HDEREF.
    unfold Ir.get_deref in HDEREF0.
    des_ifs. unfold Ir.Memory.free. rewrite Heq.
    des_ifs.
    simpl in Heq0. unfold Ir.MemBlock.inbounds in Heq0.
    rewrite PeanoNat.Nat.leb_nle in Heq0.
    exfalso. eapply Heq0. eapply n_pos.
    { inv HWF. eapply wf_blocks.
      symmetry in Heq. eapply Ir.Memory.get_In in Heq; try reflexivity.
      eassumption. }
    unfold Ir.Memory.free. des_ifs.
  }
  { unfold Ir.deref.
    rewrite HDEREF. des_ifs.
}
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
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
      clear wf_no_bogus_ptr.
      clear wf_no_bogus_ptr_mem.

      dup HPP.
      eapply physicalized_ptr_valty in HPP; try assumption.
      destruct HPP.
      { (* poison, poison *)
        inv H. inv HNEXT. inv HNEXT0.
        des_ifs; try constructor.
      }
      destruct H.
      { (* poison, ptr *)
        inv H. destruct H1. inv HNEXT.
        des_ifs; try constructor. }
      { (* ptr, ptr *)
        inv H. inv H0. inv H1.
        dup HPP0.
        eapply physicalized_ptr_get_deref with
          (sz := 1) in HPP0; try eassumption; try omega.
        inv HPP0.
        { inv H. inv H0.
          destruct x1. destruct p.
          destruct n.
          {
            apply free_get_deref in H; try assumption. rewrite H in HNEXT.
            apply free_get_deref in H1; try assumption.
            rewrite H1 in HNEXT0.
            des_ifs.
            constructor. constructor. eapply eq_incrpc2; eassumption.
            constructor.
          }
          {
            apply free_get_deref2 in H; try assumption. rewrite H in HNEXT.
            apply free_get_deref2 in H1; try assumption. rewrite H1 in HNEXT0.
            inv HNEXT. inv HNEXT0.
            constructor.
          }
        }
        { apply free_get_deref3 in H; try assumption.
          rewrite H in HNEXT. inv HNEXT.
          constructor. }
      }
    }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      congruence. }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      unfold Ir.SmallStep.t_step in HTSTEP.
      des_ifs. }
  }
  { constructor. }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
    unfold Ir.SmallStep.t_step in HTSTEP.
    des_ifs. }
Qed.


End GVN.

End Ir.

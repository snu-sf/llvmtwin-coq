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
Require Import SmallStepAux.
Require Import SmallStepWf.
Require Import Refinement.
Require Import SmallStepRefinement.
Require Import Reordering.

Module Ir.

Module GVN1.


(* Some cute lemmas *)
Lemma PTRSZ_MEMSZ:
  Nat.shiftl 2 (Ir.PTRSZ - 1) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Lemma PTRSZ_MEMSZ2:
  Nat.double (Nat.shiftl 1 (Ir.PTRSZ - 1)) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Opaque Ir.MEMSZ.
Opaque Ir.PTRSZ.

(*********** A few more useful lemmas **************)

Lemma twos_compl_MEMSZ_PTRSZ:
  forall a,
    Ir.SmallStep.twos_compl (a mod Ir.MEMSZ) Ir.PTRSZ =
    a mod Ir.MEMSZ.
Proof.
  intros.
  unfold Ir.SmallStep.twos_compl.
  rewrite PTRSZ_MEMSZ.
  rewrite Nat.mod_mod.
  reflexivity.
  assert (H := Ir.MEMSZ_pos).
  omega.
Qed.

Lemma twos_compl_sub_common_MEMSZ_PTRSZ:
  forall x y a,
    Ir.SmallStep.twos_compl_sub ((a + x) mod Ir.MEMSZ)
                                ((a + y) mod Ir.MEMSZ) Ir.PTRSZ =
    Ir.SmallStep.twos_compl_sub (x mod Ir.MEMSZ) (y mod Ir.MEMSZ) Ir.PTRSZ.
Proof.
  intros.
  apply addm_subm_eq.
  rewrite PTRSZ_MEMSZ. pose Ir.MEMSZ_pos. omega.
Qed.

Lemma OPAQUED_PTRSZ_PTRSZ:
  Ir.SmallStep.OPAQUED_PTRSZ = Ir.PTRSZ.
Proof.
  unfold Ir.SmallStep.OPAQUED_PTRSZ.
  unfold Ir.SmallStep.locked.
  des_ifs.
Qed.

Lemma p2N_addr:
  forall bid mb m ofs
         (HGET:Some mb = Ir.Memory.get m bid),
    Ir.SmallStep.p2N (Ir.plog bid ofs) m Ir.PTRSZ =
    (Ir.MemBlock.addr mb + ofs) mod Ir.MEMSZ.
Proof.
  intros.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  rewrite <- HGET.
  rewrite Nat.min_id.
  unfold Ir.SmallStep.twos_compl.
  rewrite PTRSZ_MEMSZ.
  rewrite Nat.mod_mod. reflexivity.
  assert (H := Ir.MEMSZ_pos). omega.
Qed.


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


(*********************************************************
 Specification of physicalized_ptr:
    If there is 'icmp eq p1, p2',
      and 'p2 = Phy (o, [], None)',
      and the icmp evaluates to true.
    then 'Some p2 = Ir.ptr_to_phy p1' holds.
 *********************************************************)

Theorem physicalized_ptr_spec:
  forall md st st' r ptrty op1 op2 p1 p2 o e
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iicmp_eq r ptrty op1 op2) = Ir.Config.cur_inst md st)
    (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val st op1)
    (HOP2:Some (Ir.ptr p2) = Ir.Config.get_val st op2)
    (* p2 is pphy(o, [], None) *)
    (HP2:p2 = Ir.pphy o nil None)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st'))
    (* p1 == p2 is true *)
    (HTRUE:Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r)),

    Some p2 = Ir.ptr_to_phy (Ir.Config.m st) p1.
Proof.
  intros.
  inv HSTEP.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      rewrite <- HOP1 in HNEXT.
      rewrite <- HOP2 in HNEXT.
      unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
      destruct p1 eqn:HP1.
      { (* it's log. *)
        dup HOP1.
        inv HWF. symmetry in HOP0. apply wf_ptr in HOP0.
        inv HOP0. exploit H. ss. intros HH. destruct HH as [HH1 HH2]. inv HH2.
        inv HNEXT. unfold Ir.ptr_to_phy.
        destruct (Ir.log_to_phy (Ir.Config.m st) b n) eqn:HLTP.
        { unfold Ir.log_to_phy in *. rewrite H1 in HLTP.
          inv HLTP. rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          inv HTRUE. des_ifs.
          rewrite Nat.min_id in Heq.
          rewrite twos_compl_MEMSZ_PTRSZ in Heq.
          rewrite Nat.eqb_eq in Heq.
          rewrite Heq. reflexivity.
          { unfold Ir.Config.get_rval in HTRUE.
            unfold Ir.Config.update_rval in HTRUE.
            des_ifs. congruence. }
        }
        { unfold Ir.log_to_phy in HLTP.
          des_ifs. }
      }
      { (* it's phy. *)
        inv HNEXT.
        rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
        unfold Ir.Config.get_val in HTRUE.
        rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
        inv HTRUE.
        des_ifs.
        rewrite Nat.eqb_eq in Heq.
        unfold Ir.ptr_to_phy.
        rewrite Heq.
        rewrite Nat.min_id.
        unfold Ir.SmallStep.twos_compl.
        rewrite PTRSZ_MEMSZ.
        f_equal. f_equal; try reflexivity.
        symmetry. apply Nat.mod_small.
        inv HWF.
        symmetry in HOP2. apply wf_ptr in HOP2.
        inv HOP2. exploit H1. ss. eauto.
        unfold Ir.Config.get_rval in HTRUE. unfold Ir.Config.update_rval in HTRUE.
        des_ifs. congruence.
      }
    }
    { (* well, icmp eq cannot be nondet because op2 is phy *)
      rewrite <- HINST in HCUR. inv HCUR.
      rewrite <- HOP2 in HOP3.
      inv HOP3.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET. des_ifs.
    }
  }
  { (* it's not terminator. :) *)
    apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    unfold Ir.SmallStep.t_step in HTSTEP. rewrite <- HINST in HTSTEP.
    congruence.
  }
Qed.


(*********************************************************
 Two theorems that NULL and the result of inttoptr is
 Phy(o, [], None)!
 *********************************************************)

Theorem NULL_is_vanilla_Phy:
  Ir.NULL = Ir.pphy 0 nil None.
Proof.
  reflexivity.
    Qed.

Theorem inttoptr_returns_vanilla_Phy:
  forall md st r pty (opint:Ir.op) n st' e
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iinttoptr r opint (Ir.ptrty pty)) = Ir.Config.cur_inst md st)
    (HOP1:Some (Ir.num n) = Ir.Config.get_val st opint)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st')),

  Some (Ir.ptr (Ir.pphy (Ir.SmallStep.twos_compl n Ir.PTRSZ) [] None)) =
  Ir.Config.get_val st' (Ir.opreg r).
Proof.
  intros.
  inv HSTEP.
  { inv HISTEP; try congruence.
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite <- HINST in HNEXT.
    rewrite <- HOP1 in HNEXT.
    inv HNEXT.
    rewrite Ir.SmallStep.get_val_update_reg_and_incrpc.
    unfold Ir.Config.get_val.
    rewrite Ir.Config.get_rval_update_rval_id. rewrite OPAQUED_PTRSZ_PTRSZ. reflexivity.
    { unfold Ir.Config.cur_inst in HINST.
      unfold Ir.Config.cur_fdef_pc in HINST.
      des_ifs.
    }
  }
  { (* not terminator. :)*)
    apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    unfold Ir.SmallStep.t_step in HTSTEP.
    rewrite <- HINST in HTSTEP.
    congruence.
  }
Qed.

(***** Properties of physicalized_ptr ******)

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
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t)
                                          Ir.SmallStep.OPAQUED_PTRSZ) t0)
               eqn:HINB2.
      ss.
      ss.
      ss.
      congruence.
      destruct (idx * Ir.ty_bytesz t <? Nat.shiftl 1 (Ir.SmallStep.OPAQUED_PTRSZ - 1)) eqn:HSHL.
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
                     Nat.shiftl 1 (Ir.SmallStep.OPAQUED_PTRSZ - 1))) eqn:H11.
          { (* positive offset add *)
            destruct (n + idx * Ir.ty_bytesz t <? Ir.MEMSZ) eqn:H2; try congruence.
            inversion HP2'. subst o2. subst Is2. subst cid2.
            rewrite PeanoNat.Nat.ltb_lt in H2.
            destruct (Ir.MemBlock.inbounds n0 t0 &&
                                           Ir.MemBlock.inbounds
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t)
                                          Ir.SmallStep.OPAQUED_PTRSZ) t0)
                     eqn:HINB2.
            { inversion HP1'. subst l1. subst o1.
              unfold Ir.SmallStep.twos_compl_add.
              unfold Ir.SmallStep.twos_compl.
              rewrite OPAQUED_PTRSZ_PTRSZ.
              rewrite PTRSZ_MEMSZ.
              rewrite Nat.add_mod_idemp_r.
              rewrite <- HH.
              rewrite Nat.add_mod_idemp_l.
              rewrite PeanoNat.Nat.add_assoc.
              rewrite HGETB in HGET. inv HGET. reflexivity.
              apply Ir.MEMSZ_nonzero. apply Ir.MEMSZ_nonzero.
            }
            { ss. }
          }
        { (* negaitve offset add *)
          destruct (Ir.MemBlock.inbounds n0 t0 &&
           Ir.MemBlock.inbounds
             (Ir.SmallStep.twos_compl_add n0 (idx * Ir.ty_bytesz t)
                                          Ir.SmallStep.OPAQUED_PTRSZ) t0)
                   eqn:HINB2.
          {
            inv HP2'.
            inv HP1'.
            rewrite HGETB in HGET. inv HGET.
            unfold Ir.SmallStep.twos_compl_add.
            unfold Ir.SmallStep.twos_compl.
            rewrite OPAQUED_PTRSZ_PTRSZ.
            rewrite PTRSZ_MEMSZ.
            rewrite Nat.add_mod_idemp_r.
            rewrite Nat.add_mod_idemp_l.
            rewrite PeanoNat.Nat.add_assoc. reflexivity.
            apply Ir.MEMSZ_nonzero. apply Ir.MEMSZ_nonzero.
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
        rewrite OPAQUED_PTRSZ_PTRSZ.
        rewrite PTRSZ_MEMSZ.
        rewrite Nat.add_mod_idemp_r.
        rewrite Nat.add_mod_idemp_l.
        rewrite PeanoNat.Nat.add_assoc. reflexivity.
        apply Ir.MEMSZ_nonzero. apply Ir.MEMSZ_nonzero.
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
      rewrite OPAQUED_PTRSZ_PTRSZ in H2.
      rewrite PTRSZ_MEMSZ in H2.
      rewrite Ir.MemBlock.inbounds_mod in Heq2; try assumption.
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
        assert (HH := Ir.MemBlock.blocksz_lt t0 H3).
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
      rewrite <- PTRSZ_MEMSZ2. unfold Nat.double.
      rewrite OPAQUED_PTRSZ_PTRSZ in *.
      omega.
      inv HWF. eapply wf_blocks.
      eapply Ir.Memory.get_In. rewrite Heq. reflexivity. reflexivity.
    }
    { eapply physicalized_ptr_phy in HPP; try reflexivity.
      destruct HPP. destruct H2. subst n0. subst o.
      congruence.
    }
  }
Qed.
      

(**** lemmas regarding twos_compl_add and inbounds_abs *****)

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
    apply Ir.MEMSZ_nonzero.
    apply Ir.MEMSZ_nonzero.
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
    apply Ir.MEMSZ_nonzero.
    apply Ir.MEMSZ_nonzero.
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


(***** A few lemmas about physicalized_ptr ******)

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
        rewrite OPAQUED_PTRSZ_PTRSZ in *.
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
        rewrite OPAQUED_PTRSZ_PTRSZ in *.
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






(* ends with refinement with common update_reg_and_incrpc calls *)
Ltac thats_it :=
          eapply Ir.SSRefinement.refines_update_reg_and_incrpc;
            try eassumption;
          [ apply Ir.Refinement.refines_state_eq;
            apply Ir.Config.eq_refl
          | try apply Ir.Refinement.refines_value_refl; constructor; fail ].

Ltac cc_thats_it := constructor; constructor; thats_it.

(* ends with refinement with common incrpc calls *)
Ltac thats_it2 :=
          eapply Ir.SSRefinement.refines_incrpc;
            try eassumption;
          apply Ir.Refinement.refines_state_eq;
          apply Ir.Config.eq_refl.

Ltac cc_thats_it2 := constructor; constructor; thats_it2.

Ltac hey_terminator HINST2 :=
  apply Ir.Config.cur_inst_not_cur_terminator in HINST2;
       congruence.

Ltac hey_terminator2 HINST2 HTSTEP :=
  apply Ir.Config.cur_inst_not_cur_terminator in HINST2;
       unfold Ir.SmallStep.t_step in HTSTEP;
       des_ifs.

Ltac unfold_all_ands_H :=
  repeat (match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  end).





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
      clear wf_ptr.
      clear wf_ptr_mem.

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
          erewrite Ir.load_val_get_deref with (ptr2 := x);
            try congruence.
          thats_it.
        }
        { (* src fails *)
          unfold Ir.deref in *.
          rewrite H in HNEXT. inv HNEXT. constructor.
        }
        apply Ir.ty_bytesz_pos.
      }
      inv HWF2. assumption.
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
      clear wf_ptr.
      clear wf_ptr_mem.

      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP.
      { (* poison, poison *)
        inv H. inv HNEXT. inv HNEXT0.
        des_ifs; constructor. constructor.
        thats_it2.
      }
      destruct H.
      { (* poison, ptr *)
        inv H. destruct H1. inv HNEXT.
        des_ifs; try constructor. constructor.
        thats_it2. }
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
          erewrite Ir.store_val_get_deref with (ptr2 := x);
            try congruence.
          thats_it2.
          constructor.
          thats_it2.
        }
        { (* src fails *)
          unfold Ir.deref in *.
          rewrite H in HNEXT.
          des_ifs; try constructor.
          constructor.
          thats_it2.
        }
        apply Ir.ty_bytesz_pos.
      }
      inv HWF2. assumption.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  { constructor. }
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on free instruction.
 *****)

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
    erewrite Ir.Memory.zeroofs_block_addr. reflexivity.
    assumption. assumption.
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
    exfalso. eapply Heq0. eapply Ir.MemBlock.n_pos.
    { inv HWF. eapply wf_blocks.
      symmetry in Heq. eapply Ir.Memory.get_In in Heq; try reflexivity.
      eassumption. }
    unfold Ir.Memory.free. des_ifs.
  }
  { unfold Ir.deref.
    rewrite HDEREF. des_ifs.
}
Qed.

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
      clear wf_ptr.
      clear wf_ptr_mem.

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
            constructor. constructor.
            thats_it2.
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
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.
  }
  { constructor. }
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
      clear wf_ptr.
      clear wf_ptr_mem.
      inv HNEXT. inv HNEXT0.
      destruct retty; try
       (constructor; constructor; thats_it).
      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP;
        unfold_all_ands_H; ss.
      { inv H. constructor. constructor. thats_it. }
      destruct H.
      { destruct H. destruct H0. inv H.
        constructor. constructor. thats_it. }
      { destruct H. destruct H. destruct H0. inv H.
        destruct x0.
        { eapply physicalized_ptr_nonlog in HPP0.
          exfalso. apply HPP0. eexists. eexists. reflexivity. }
        destruct x.
        { (* log, phy *)
          dup HPP0.
          eapply physicalized_ptr_log_get in HPP0; try reflexivity;
            try eassumption.
          destruct HPP0.
          eapply physicalized_ptr_convert in HPP1; try reflexivity; try eassumption.
          unfold Ir.SmallStep.p2N.
          unfold Ir.log_to_phy. rewrite <- H.
          rewrite HPP1.
          constructor. constructor. thats_it.
        }
        { (* phy, phy *)
          eapply physicalized_ptr_phy in HPP0; try reflexivity.
          unfold_all_ands_H; ss.
          subst n0.
          constructor. constructor. thats_it.
        }
      }
      inv HWF2. assumption.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.    
  }
  { constructor. }
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
      clear wf_ptr_mem.
      inv HNEXT. inv HNEXT0.
      destruct retty; try
       (constructor; constructor; thats_it).
      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP;
        unfold_all_ands_H; ss.
      { inv H. constructor. constructor. thats_it. }
      destruct H.
      { destruct H. destruct H0. inv H.
        constructor. constructor.
        des_ifs;try thats_it.
        eapply Ir.SSRefinement.refines_update_reg_and_incrpc;
          try eassumption.
        eapply Ir.Refinement.refines_state_eq.
          apply Ir.Config.eq_refl.
        unfold Ir.Refinement.refines_value.
        des_ifs. }
      { destruct H. destruct H. destruct H0. inv H.
        destruct x0.
        { eapply physicalized_ptr_nonlog in HPP0.
          exfalso. apply HPP0. eexists. eexists. reflexivity. }
        destruct x.
        { (* log, phy *)
          dup HPP0.
          eapply physicalized_ptr_log_get in HPP0; try reflexivity;
            try eassumption.
          destruct HPP0.
          des_ifs; try (cc_thats_it).
          eapply physicalized_ptr_convert in HPP1; try reflexivity; try eassumption.
          unfold Ir.SmallStep.psub.
          destruct p.
          { destruct (b =? b0) eqn:HEQ.
            { rewrite PeanoNat.Nat.eqb_eq in HEQ. subst b.
              rewrite OPAQUED_PTRSZ_PTRSZ.
              rewrite p2N_addr with (mb := x).
              rewrite <- HPP1.
              assert (HN1: n1 = n1 mod Ir.MEMSZ).
              { rewrite Nat.mod_small. reflexivity.
                eapply wf_ptr in HOP1. inv HOP1. exploit H0. ss. intros HH. intuition. }
              assert (HN2: n2 = n2 mod Ir.MEMSZ).
              { rewrite Nat.mod_small. reflexivity.
                eapply wf_ptr in Heq. inv Heq. exploit H0. ss. intros HH. intuition. }
              rewrite HN1 at 2.
              rewrite HN2 at 2.
              rewrite twos_compl_sub_common_MEMSZ_PTRSZ.
              constructor. constructor. thats_it.
              congruence.
            }
            { (* poison *) constructor. constructor. thats_it. }
          }
          { (* log,phy*)
            rewrite OPAQUED_PTRSZ_PTRSZ.
            rewrite p2N_addr with (mb := x).
            rewrite <- HPP1.
            constructor. constructor. thats_it.
            congruence.
          }
        }
        { (* phy, phy *)
          eapply physicalized_ptr_phy in HPP0; try reflexivity.
          unfold_all_ands_H; ss.
          subst n0.
          unfold Ir.SmallStep.psub.
          des_ifs; try (constructor; constructor; thats_it).
        }
      }
      inv HWF2. assumption.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.    
  }
  { constructor. }
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
      clear wf_ptr_mem.
      inv HNEXT. inv HNEXT0.
      destruct retty; try
       (constructor; constructor; thats_it).
      dup HPP.
      eapply physicalized_ptr_valty in HPP.
      destruct HPP;
        unfold_all_ands_H; ss.
      { inv H. constructor. constructor. thats_it. }
      destruct H.
      { destruct H. destruct H0. inv H.
        constructor. constructor.
        des_ifs;try thats_it.
        eapply Ir.SSRefinement.refines_update_reg_and_incrpc;
          try eassumption.
        eapply Ir.Refinement.refines_state_eq.
          apply Ir.Config.eq_refl.
        unfold Ir.Refinement.refines_value.
        des_ifs. }
      { destruct H. destruct H. destruct H0. inv H.
        destruct x0.
        { eapply physicalized_ptr_nonlog in HPP0.
          exfalso. apply HPP0. eexists. eexists. reflexivity. }
        destruct x.
        { (* log, phy *)
          dup HPP0.
          eapply physicalized_ptr_log_get in HPP0; try reflexivity;
            try eassumption.
          destruct HPP0.
          des_ifs; try (cc_thats_it).
          eapply physicalized_ptr_convert in HPP1; try reflexivity; try eassumption.
          unfold Ir.SmallStep.psub.
          destruct p.
          { destruct (b0 =? b) eqn:HEQ.
            { rewrite PeanoNat.Nat.eqb_eq in HEQ. subst b.
              rewrite OPAQUED_PTRSZ_PTRSZ.
              rewrite p2N_addr with (mb := x).
              rewrite <- HPP1.
              assert (HN1: n1 = n1 mod Ir.MEMSZ).
              { rewrite Nat.mod_small. reflexivity.
                eapply wf_ptr in HOP1. inv HOP1. exploit H0.
                ss. intros HH. intuition. }
              assert (HN2: n2 = n2 mod Ir.MEMSZ).
              { rewrite Nat.mod_small. reflexivity.
                eapply wf_ptr in Heq. inv Heq. exploit H0.
                ss. intros HH. intuition. }
              rewrite HN1 at 2.
              rewrite HN2 at 2.
              rewrite twos_compl_sub_common_MEMSZ_PTRSZ.
              constructor. constructor. thats_it.
              congruence.
            }
            { (* poison *) constructor. constructor. thats_it. }
          }
          { (* log,phy*)
            rewrite OPAQUED_PTRSZ_PTRSZ.
            rewrite p2N_addr with (mb := x).
            rewrite <- HPP1.
            constructor. constructor. thats_it.
            congruence.
          }
        }
        { (* phy, phy *)
          eapply physicalized_ptr_phy in HPP0; try reflexivity.
          unfold_all_ands_H; ss.
          subst n0.
          unfold Ir.SmallStep.psub.
          des_ifs; try (constructor; constructor; thats_it).
        }
      }
      inv HWF2. assumption.
    }
    hey_terminator HINST2.
    hey_terminator2 HINST2 HTSTEP.    
  }
  { constructor. }
  hey_terminator2 HINST1 HTSTEP.
Qed.



(*****
      Refinement on icmp eq instruction.
 *****)
Lemma physicalized_ptr_icmp_eq_nondet:
  forall md st b0 b1 mb1 mb2 n0 n1 n l o
         (HWF:Ir.Config.wf md st)
         (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st) b0)
         (HGET1:Some mb2 = Ir.Memory.get (Ir.Config.m st) b1)
         (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog b0 n0) 
              (Ir.plog b1 n1) (Ir.Config.m st) = false)
         (HDIFFBLK: b0 =? b1 = false)
         (HPP: physicalized_ptr (Ir.Config.m st) (Ir.ptr (Ir.plog b0 n0))
              (Ir.ptr (Ir.pphy n l o))),
  Ir.SmallStep.icmp_eq_ptr (Ir.pphy n l o) (Ir.plog b1 n1) (Ir.Config.m st) =
    Some false.
Proof.
  intros.
  eapply physicalized_ptr_convert in HPP; try reflexivity; try eassumption.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
  rewrite <- HGET1, <- HGET0 in HNONDET.
  rewrite HDIFFBLK in HNONDET. simpl in HNONDET.
  repeat (rewrite orb_false_iff in HNONDET).
  destruct HNONDET as [[[[HN1 HN2] HN3] HN4] HN5].
  rewrite andb_false_iff in HN1.
  rewrite andb_false_iff in HN3.
  repeat (rewrite Nat.eqb_neq in *).
  repeat (rewrite Nat.ltb_ge in *).
  unfold Ir.SmallStep.icmp_eq_ptr.
  rewrite p2N_addr with (mb := mb2); try congruence.
  assert (n = Ir.MemBlock.addr mb1 + n0).
  { rewrite <- HPP.
    apply Nat.mod_small.
    inv HWF. inv wf_m.
    eapply Ir.Memory.get_In in HGET1; try reflexivity.
    apply wf_blocks in HGET1.
    dup HGET1. inv HGET1.
    assert (Ir.MemBlock.addr mb1 + Ir.MemBlock.n mb1 < Ir.MEMSZ).
    { eapply wf_inmem. apply Ir.MemBlock.addr_P_In. assumption. }
    omega.
  }
  rewrite H.
  assert (Ir.MemBlock.addr mb2 + n1 = (Ir.MemBlock.addr mb2 + n1) mod Ir.MEMSZ).
  { symmetry. apply Nat.mod_small.
    inv HWF. inv wf_m.
    eapply Ir.Memory.get_In in HGET0; try reflexivity.
    apply wf_blocks in HGET0.
    dup HGET0. inv HGET0.
    assert (Ir.MemBlock.addr mb2 + Ir.MemBlock.n mb2 < Ir.MEMSZ).
    { eapply wf_inmem. apply Ir.MemBlock.addr_P_In. assumption. }
    omega.
  }
  rewrite <- H0.
  assert (HDISJ_TMP:disjoint_ranges
                      ((Ir.MemBlock.P_ranges mb1) ++Ir.MemBlock.P_ranges mb2) = true).
  { inv HWF. inv wf_m.
    eapply wf_disjoint2.
    { eapply HGET1. }
    { eapply HGET0. }
    { congruence. }
    { unfold disjoint_range.
      unfold Ir.MemBlock.lifetime_to_range.
      destruct (Ir.MemBlock.r mb1) as (tb1, te1) eqn:HR1.
      destruct (Ir.MemBlock.r mb2) as (tb2, te2) eqn:HR2.
      simpl in *.
      destruct te1; destruct te2.
      { rewrite orb_false_iff in *.
        repeat (rewrite Nat.leb_gt in HN5).
        destruct HN5.
        eapply Ir.Memory.get_In in HGET1; try reflexivity.
        eapply Ir.Memory.get_In in HGET0; try reflexivity.
        eapply wf_blocktime_end in HGET1.
        2: rewrite HR1; reflexivity.
        eapply wf_blocktime_end in HGET0.
        2: rewrite HR2; reflexivity.
        rewrite HR1 in HGET1. simpl in HGET1.
        rewrite HR2 in HGET0. simpl in HGET0.
        split; rewrite Nat.leb_gt; omega.
      }
      { rewrite orb_false_iff in *.
        rewrite Nat.leb_gt in HN5.
        eapply Ir.Memory.get_In in HGET1; try reflexivity.
        eapply wf_blocktime_end in HGET1.
        2: rewrite HR1; reflexivity.
        rewrite HR1 in HGET1. simpl in HGET1.
        split; rewrite Nat.leb_gt; omega.
      }
      { rewrite orb_false_iff in *.
        rewrite Nat.leb_gt in HN5.
        eapply Ir.Memory.get_In in HGET0; try reflexivity.
        eapply wf_blocktime_end in HGET0.
        2: rewrite HR2; reflexivity.
        rewrite HR2 in HGET0. simpl in HGET0.
        split; rewrite Nat.leb_gt; omega.
      }
      { rewrite orb_false_iff.
        eapply Ir.Memory.get_In in HGET1; try reflexivity.
        eapply Ir.Memory.get_In in HGET0; try reflexivity.
        eapply wf_blocktime_beg in HGET1.
        eapply wf_blocktime_beg in HGET0.
        rewrite HR1 in HGET1. simpl in HGET1.
        rewrite HR2 in HGET0. simpl in HGET0.
        split; rewrite Nat.leb_gt; omega.
      }
    }
  }
  assert (HDISJ:disjoint_ranges ([Ir.MemBlock.P0_range mb1] ++ [Ir.MemBlock.P0_range mb2])
                          = true).
  { eapply disjoint_lsubseq_disjoint.
    eapply HDISJ_TMP.
    eapply lsubseq_append.
    { eapply Ir.MemBlock.P_P0_range_lsubseq.
      inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In. eassumption. reflexivity. }
    { eapply Ir.MemBlock.P_P0_range_lsubseq.
      inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In. eassumption. reflexivity. }
  }
  simpl in HDISJ.
  unfold disjoint_range in HDISJ.
  unfold Ir.MemBlock.P0_range in HDISJ.
  repeat (rewrite andb_true_r in HDISJ).
  rewrite orb_true_iff in HDISJ.
  repeat (rewrite Nat.leb_le in HDISJ).
  remember (Ir.MemBlock.addr mb1 + n0 =? Ir.MemBlock.addr mb2 + n1) as res.
  destruct res.
  { symmetry in Heqres. rewrite Nat.eqb_eq in Heqres.
    destruct HDISJ; destruct HN1; destruct HN3; omega.
  }
  { reflexivity. }
Qed.


Lemma log_ofs_lt_MEMSZ:
  forall st opptr b1 n1
         (Hwf_ptr:forall (op : Ir.op) (p : Ir.ptrval),
           Ir.Config.get_val st op = Some (Ir.ptr p) -> Ir.Config.ptr_wf p (Ir.Config.m st))
         (Hop:Ir.Config.get_val st opptr = Some (Ir.ptr (Ir.plog b1 n1))),
    n1 < Ir.MEMSZ.
Proof.
  intros.
  apply Hwf_ptr in Hop. inv Hop. exploit H. ss. intros.
  intuition.
Qed.

Lemma phy_ofs_lt_MEMSZ:
  forall st opptr o I cid
         (Hwf_ptr:forall (op : Ir.op) (p : Ir.ptrval),
           Ir.Config.get_val st op = Some (Ir.ptr p) -> Ir.Config.ptr_wf p (Ir.Config.m st))
         (Hop:Ir.Config.get_val st opptr = Some (Ir.ptr (Ir.pphy o I cid))),
    o < Ir.MEMSZ.
Proof.
  intros.
  apply Hwf_ptr in Hop. inv Hop. exploit H0. ss. intros.
  omega.
Qed.

Theorem icmp_eq_refines_l:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr11 opptr12 opptr2 ptrty v1 v2 sr2
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
         (* And.. have a step. *)
         (* Note that icmp has nondet. semantics, so we should use
            exists quantifier. *)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    exists sr1,
         Ir.SmallStep.sstep md1 st sr1 /\
         Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP2.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST2 in HNEXT.
      rewrite HOP2 in HNEXT.
      dup HPP. dup HPP.
      eapply physicalized_ptr_valty in HPP.
      inv HPP.
      { (* poison, poison *)
        inv H. inv HNEXT.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite <- HINST1. rewrite HOP1. reflexivity. }
        { constructor. constructor. thats_it. }
      }
      inv H.
      { (* poison, ptr *)
        inv H0. inv H1.
        des_ifs;
        ( eexists; split;
          [ eapply Ir.SmallStep.ss_inst; eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite <- HINST1; rewrite HOP1; reflexivity
          | constructor; constructor; thats_it ]
        ).
      }
      { (* ptr, ptr *)
        inv H0. inv H. inv H1.
        des_ifs.
        { eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { constructor. constructor. thats_it. }
        }
        { destruct x0.
          { eapply physicalized_ptr_nonlog in HPP0. exfalso.
            eapply HPP0. eexists. eexists. reflexivity. }
          destruct x.
          { destruct p.
            { (* src: icmp eq log, log
                 tgt: icmp eq phy, log *)
              destruct (b0 =? b1) eqn:HSAMEBLK.
              { rewrite PeanoNat.Nat.eqb_eq in HSAMEBLK.
                subst b0.
                (* deterministic! *)
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                  unfold Ir.SmallStep.inst_det_step.
                  rewrite <- HINST1.
                  rewrite HOP1. rewrite Heq.
                  unfold Ir.SmallStep.icmp_eq_ptr in *.
                  rewrite PeanoNat.Nat.eqb_refl.
                  reflexivity. }
                { constructor. constructor.
                  unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                  dup HOP1.
                  (* convert p2N into (addr + ofs). *)
                  inv HWF1.
                  apply wf_ptr in HOP1.
                  inv HOP1. exploit H. ss. intros HH. inv HH. inv H2.
                  eapply physicalized_ptr_convert with (mb := x)
                    in HPP0; try reflexivity; try congruence.
                  rewrite p2N_addr with (mb := x) in Heq0.
                  rewrite <- HPP0 in Heq0.
                  inv Heq0.
                  (* make log1 ofs < MEMSZ, log2 ofs < MEMSZ. *)
                  assert (n0 =? n1 = (n0 mod Ir.MEMSZ =? n1 mod Ir.MEMSZ)).
                  { rewrite <- Nat.mod_small with (a := n0) (b := Ir.MEMSZ) at 1.
                    rewrite <- Nat.mod_small with (a := n1) (b := Ir.MEMSZ) at 1.
                    reflexivity. eapply log_ofs_lt_MEMSZ; eassumption.
                    eapply log_ofs_lt_MEMSZ; eassumption.
                  }
                  rewrite H2.
                  rewrite mod_add_eq.
                  thats_it.
                  apply Ir.MEMSZ_pos. congruence.
                }
              }
              { (* different blocks!. *)
                destruct (Ir.SmallStep.icmp_eq_ptr_nondet_cond
                            (Ir.plog b0 n0) (Ir.plog b1 n1) (Ir.Config.m st))
                         eqn:HNONDET.
                { (* yes~! *)
                  eexists.
                  split.
                  { eapply Ir.SmallStep.ss_inst.
                    eapply Ir.SmallStep.s_icmp_eq_nondet; try eassumption;
                      try reflexivity.
                    rewrite HOP1. reflexivity.
                    rewrite Heq. reflexivity. }
                  { unfold Ir.SmallStep.to_num.
                    constructor. constructor. thats_it. }
                }
                { (* no.. *)
                  eexists. split.
                  { eapply Ir.SmallStep.ss_inst.
                    eapply Ir.SmallStep.s_det.
                    unfold Ir.SmallStep.inst_det_step.
                    rewrite <- HINST1. rewrite Heq.
                    rewrite HOP1.
                    unfold Ir.SmallStep.icmp_eq_ptr.
                    rewrite HSAMEBLK.
                    rewrite HNONDET. reflexivity. }
                  { (* okay.. icmp eq phy log should be false. *)
                    inv HWF1.
                    eapply wf_ptr in HOP1. inv HOP1.
                    exploit H. ss. intros HH. inv HH. inv H2.
                    eapply wf_ptr in Heq. inv Heq.
                    exploit H2. ss. intros HH. inv HH. inv H6.
                    eapply physicalized_ptr_icmp_eq_nondet in HNONDET; try eassumption.
                    { rewrite Heq0 in HNONDET. inv HNONDET.
                      constructor. constructor. thats_it. }
                    { rewrite H3. reflexivity. }
                    { rewrite H7. reflexivity. }
                  }
                }
              }
            }
            { (* log == phy -> phy == phy *)
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step.
                rewrite <- HINST1. rewrite HOP1, Heq.
                unfold Ir.SmallStep.icmp_eq_ptr.
                reflexivity.
              }
              { inv HWF1. eapply wf_ptr in HOP1. destruct HOP1.
                exploit H. ss. intros HH. inv HH. inv H2.
                eapply physicalized_ptr_convert in HPP1; try reflexivity.
                2: rewrite H3; reflexivity.
                unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                inv Heq0. unfold Ir.SmallStep.p2N. unfold Ir.log_to_phy.
                rewrite H3. rewrite Nat.min_id.
                rewrite twos_compl_MEMSZ_PTRSZ.
                assert (n1 = n1 mod Ir.MEMSZ).
                { symmetry. apply Nat.mod_small.
                  eapply phy_ofs_lt_MEMSZ; eassumption. }
                rewrite H2. rewrite twos_compl_MEMSZ_PTRSZ.
                constructor. constructor. thats_it.
              }
            }
          }
          { (* phy, phy *)
            eapply physicalized_ptr_phy in HPP1; try reflexivity.
            inv HPP1. inv H0.
            eexists. split.
            { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
              rewrite HOP1. rewrite Heq.
              unfold Ir.SmallStep.icmp_eq_ptr in *.
              reflexivity.
            }
            { unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
              inv Heq0. constructor. constructor. thats_it. }
          }
        }
        { (* poison *)
          eexists. eexists.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq.
            reflexivity.
          }
          { cc_thats_it. }
        }
        { (* poison *)
          eexists. eexists.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq.
            reflexivity.
          }
          { cc_thats_it. }
        }
      }
      { inv HWF1. ss. }
    }
    { (* nondet check is true. *)
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP0. inv HOP0. dup HPP.
      apply physicalized_ptr_valty in HPP.
      inv HPP.
      { inv H. inv H1. }
      inv H.
      { inv H0. inv H1. inv H.
        do 2 eexists.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
          rewrite HOP1. reflexivity. }
        { cc_thats_it. }
      }
      { inv H0. inv H. inv H1. inv H.
        (* nondet check cannot be true! *)
        dup HPP0.
        apply physicalized_ptr_nonlog in HPP0. exfalso. eapply HPP0.
        unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
        des_ifs; do 2 eexists; reflexivity.
      }
      { inv HWF1. assumption. }
    }
  }
  { hey_terminator HINST2. }
  { hey_terminator2 HINST2 HTSTEP.  }
Qed.

Lemma icmp_eq_ptr_nondet_cond_sym:
  forall p1 p2 m,
    Ir.SmallStep.icmp_eq_ptr_nondet_cond p1 p2 m = Ir.SmallStep.icmp_eq_ptr_nondet_cond p2 p1 m.
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
  des_ifs.
  { replace (b =? b0) with (b0 =? b) by apply Nat.eqb_sym.
    apply andb_inj_r.
    destruct (n =? Ir.MemBlock.n t);
      destruct (n0 =? 0); destruct (Ir.MemBlock.n t <? n);
        destruct (n =? 0); destruct (n0 =? Ir.MemBlock.n t0);
          destruct (Ir.MemBlock.n t0 <? n0);
          destruct (t2 <=? t3); destruct (t4 <=? t1); reflexivity.
  }
  { replace (b =? b0) with (b0 =? b) by apply Nat.eqb_sym.
    apply andb_inj_r.
    destruct (n =? Ir.MemBlock.n t);
      destruct (n0 =? 0); destruct (Ir.MemBlock.n t <? n);
        destruct (n =? 0); destruct (n0 =? Ir.MemBlock.n t0);
          destruct (Ir.MemBlock.n t0 <? n0);
          destruct (t2 <=? t3); reflexivity.
  }
  { replace (b =? b0) with (b0 =? b) by apply Nat.eqb_sym.
    apply andb_inj_r.
    destruct (n =? Ir.MemBlock.n t);
      destruct (n0 =? 0); destruct (Ir.MemBlock.n t <? n);
        destruct (n =? 0); destruct (n0 =? Ir.MemBlock.n t0);
          destruct (Ir.MemBlock.n t0 <? n0);
          destruct (t3 <=? t1); reflexivity.
  }
  { replace (b =? b0) with (b0 =? b) by apply Nat.eqb_sym.
    apply andb_inj_r.
    destruct (n =? Ir.MemBlock.n t);
      destruct (n0 =? 0); destruct (Ir.MemBlock.n t <? n);
        destruct (n =? 0); destruct (n0 =? Ir.MemBlock.n t0);
          destruct (Ir.MemBlock.n t0 <? n0); reflexivity.
  }
Qed.

Lemma icmp_eq_ptr_sym:
  forall md p1 p2 st op1 op2
         (HWF:Ir.Config.wf md st)
         (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val st op1)
         (HOP1:Some (Ir.ptr p2) = Ir.Config.get_val st op2),
    Ir.SmallStep.icmp_eq_ptr p1 p2 (Ir.Config.m st) =
    Ir.SmallStep.icmp_eq_ptr p2 p1 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_eq_ptr.
  des_ifs;
  try (rewrite Nat.eqb_sym; reflexivity);
  try (rewrite Nat.eqb_sym in Heq; congruence);
  try (rewrite icmp_eq_ptr_nondet_cond_sym in Heq0; congruence).
  unfold Ir.SmallStep.p2N.
  assert (n = n mod Ir.MEMSZ).
  { inv HWF. symmetry in HOP1. symmetry. apply Nat.mod_small.
    eapply phy_ofs_lt_MEMSZ; eassumption. }
  assert (n0 = n0 mod Ir.MEMSZ).
  { inv HWF. symmetry in HOP0. symmetry. apply Nat.mod_small.
    eapply phy_ofs_lt_MEMSZ; eassumption. }
  rewrite H.
  rewrite H0.
  rewrite Nat.eqb_sym.
  rewrite twos_compl_MEMSZ_PTRSZ.
  rewrite twos_compl_MEMSZ_PTRSZ.
  reflexivity.
Qed.

Theorem icmp_eq_refines_r:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr21 opptr22 ptrty v1 v2 sr2
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
         (* And.. have a step. *)
         (* Note that icmp has nondet. semantics, so we should use
            exists quantifier. *)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    exists sr1,
         Ir.SmallStep.sstep md1 st sr1 /\
         Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP2.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST2 in HNEXT.
      rewrite HOP2 in HNEXT.
      dup HPP. dup HPP.
      eapply physicalized_ptr_valty in HPP.
      inv HPP.
      { (* poison, poison *)
        inv H. inv HNEXT.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite <- HINST1. rewrite HOP1.
          des_ifs; reflexivity. }
        { des_ifs;
          constructor; constructor; thats_it. }
      }
      inv H.
      { (* poison, ptr *)
        inv H0. inv H1.
        des_ifs;
        ( eexists; split;
          [ eapply Ir.SmallStep.ss_inst; eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite <- HINST1; rewrite HOP1; des_ifs; reflexivity
          | des_ifs; constructor; constructor; thats_it ]
        ).
      }
      { (* ptr, ptr *)
        inv H0. inv H. inv H1.
        des_ifs.
        { eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { constructor. constructor. thats_it. }
        }
        { destruct x0.
          { eapply physicalized_ptr_nonlog in HPP0. exfalso.
            eapply HPP0. eexists. eexists. reflexivity. }
          destruct x.
          { destruct p.
            { (* src: icmp eq log, log
                 tgt: icmp eq log, phy *)
              destruct (b0 =? b1) eqn:HSAMEBLK.
              { rewrite PeanoNat.Nat.eqb_eq in HSAMEBLK.
                subst b0.
                (* deterministic! *)
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                  unfold Ir.SmallStep.inst_det_step.
                  rewrite <- HINST1.
                  rewrite HOP1. rewrite Heq.
                  unfold Ir.SmallStep.icmp_eq_ptr in *.
                  rewrite PeanoNat.Nat.eqb_refl.
                  reflexivity. }
                { constructor. constructor.
                  unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                  dup HOP1.
                  (* convert p2N into (addr + ofs). *)
                  inv HWF1.
                  apply wf_ptr in HOP1.
                  inv HOP1. exploit H. ss. intros HH. inv HH. inv H2.
                  eapply physicalized_ptr_convert with (mb := x)
                    in HPP0; try reflexivity; try congruence.
                  rewrite p2N_addr with (mb := x) in Heq0.
                  rewrite <- HPP0 in Heq0.
                  inv Heq0.
                  (* make log1 ofs < MEMSZ, log2 ofs < MEMSZ. *)
                  assert (n1 =? n0 = (n1 mod Ir.MEMSZ =? n0 mod Ir.MEMSZ)).
                  { rewrite <- Nat.mod_small with (a := n0) (b := Ir.MEMSZ) at 1.
                    rewrite <- Nat.mod_small with (a := n1) (b := Ir.MEMSZ) at 1.
                    reflexivity.
                    eapply log_ofs_lt_MEMSZ; eassumption.
                    eapply log_ofs_lt_MEMSZ; eassumption.
                  }
                  rewrite H2.
                  rewrite mod_add_eq.
                  thats_it.
                  apply Ir.MEMSZ_pos. congruence.
                }
              }
              { (* different blocks!. *)
                destruct (Ir.SmallStep.icmp_eq_ptr_nondet_cond
                            (Ir.plog b1 n1) (Ir.plog b0 n0) (Ir.Config.m st))
                         eqn:HNONDET.
                { (* yes~! *)
                  eexists.
                  split.
                  { eapply Ir.SmallStep.ss_inst.
                    eapply Ir.SmallStep.s_icmp_eq_nondet; try eassumption;
                      try reflexivity.
                    rewrite Heq. reflexivity.
                    rewrite HOP1. reflexivity. }
                  { unfold Ir.SmallStep.to_num.
                    constructor. constructor. thats_it. }
                }
                { (* no.. *)
                  eexists. split.
                  { eapply Ir.SmallStep.ss_inst.
                    eapply Ir.SmallStep.s_det.
                    unfold Ir.SmallStep.inst_det_step.
                    rewrite <- HINST1. rewrite Heq.
                    rewrite HOP1.
                    unfold Ir.SmallStep.icmp_eq_ptr.
                    rewrite Nat.eqb_sym in HSAMEBLK.
                    rewrite HSAMEBLK.
                    rewrite HNONDET. reflexivity. }
                  { (* okay.. icmp eq phy log should be false. *)
                    inv HWF1. dup Heq.
                    eapply wf_ptr in HOP1. inv HOP1. exploit H. ss. intros HH.
                    inv HH. inv H2.
                    eapply wf_ptr in Heq. inv Heq. exploit H2. ss. intros HH.
                    inv HH. inv H6.
                    rewrite icmp_eq_ptr_nondet_cond_sym in HNONDET.
                    eapply physicalized_ptr_icmp_eq_nondet in HNONDET
                    ; try eassumption.
                    { erewrite icmp_eq_ptr_sym in HNONDET; try eassumption.
                      rewrite Heq0 in HNONDET. inv HNONDET.
                      constructor. constructor. thats_it.
                      rewrite HOP2. reflexivity. rewrite Heq1. reflexivity. }
                    { eauto. }
                    { eauto. }
                  }
                }
              }
            }
            { (* log == phy -> phy == phy *)
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step.
                rewrite <- HINST1. rewrite HOP1, Heq.
                unfold Ir.SmallStep.icmp_eq_ptr.
                reflexivity.
              }
              { inv HWF1. eapply wf_ptr in HOP1. destruct HOP1. exploit H.
                ss. intros HH. inv HH. inv H2.
                eapply physicalized_ptr_convert in HPP1; try reflexivity.
                2: eauto.
                unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                inv Heq0. unfold Ir.SmallStep.p2N. unfold Ir.log_to_phy.
                rewrite H3. rewrite Nat.min_id.
                rewrite twos_compl_MEMSZ_PTRSZ.
                assert (n1 = n1 mod Ir.MEMSZ).
                { symmetry. apply Nat.mod_small.
                  eapply phy_ofs_lt_MEMSZ; eassumption. }
                rewrite H2.
                constructor. constructor. thats_it.
              }
            }
          }
          { (* phy, phy *)
            eapply physicalized_ptr_phy in HPP1; try reflexivity.
            destruct p.
            { inv HPP1. inv H0.
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                rewrite HOP1. rewrite Heq.
                unfold Ir.SmallStep.icmp_eq_ptr in *.
                reflexivity.
              }
              { unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                inv Heq0. constructor. constructor. thats_it. }
            }
            { inv HPP1. inv H0.
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                rewrite HOP1. rewrite Heq.
                unfold Ir.SmallStep.icmp_eq_ptr in *.
                reflexivity.
              }
              { unfold Ir.SmallStep.icmp_eq_ptr in Heq0.
                inv Heq0. constructor. constructor. thats_it. }
            }
          }
        }
        { (* poison *)
          eexists. eexists.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq.
            reflexivity.
          }
          { cc_thats_it. }
        }
        { (* poison *)
          eexists. eexists.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq.
            reflexivity.
          }
          { cc_thats_it. }
        }
      }
      { inv HWF1. ss. }
    }
    { (* nondet check is true. *)
      rewrite <- HINST2 in HCUR. inv HCUR.
      rewrite HOP2 in HOP3. inv HOP3. dup HPP.
      apply physicalized_ptr_valty in HPP.
      inv HPP.
      { inv H. inv H1. }
      inv H.
      { inv H0. inv H1. inv H.
        do 2 eexists.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
          rewrite HOP1. rewrite <- HOP0. reflexivity. }
        { cc_thats_it. }
      }
      { inv H0. inv H. inv H1. inv H.
        (* nondet check cannot be true! *)
        dup HPP0.
        apply physicalized_ptr_nonlog in HPP0. exfalso. eapply HPP0.
        unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
        des_ifs; do 2 eexists; reflexivity.
      }
      { inv HWF1. assumption. }
    }
  }
  { hey_terminator HINST2. }
  { hey_terminator2 HINST2 HTSTEP.  }
Qed.


(*****
      Refinement on icmp ule instruction.
 *****)

Lemma leb_add:
  forall n x y,
    (n + x <=? n + y) = (x <=? y).
Proof.
  intros.
  destruct (n+x <=? n+y) eqn:H1;
    destruct (x <=? y) eqn:H2; try reflexivity.
  { rewrite Nat.leb_le in *. 
    rewrite Nat.leb_gt in *. omega. }
  { rewrite Nat.leb_le in *. 
    rewrite Nat.leb_gt in *. omega. }
Qed.

Lemma physicalized_ptr_icmp_ule_nondet:
  forall md st b0 b1 mb1 mb2 n0 n1 n l o
     (HWF:Ir.Config.wf md st)
     (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st) b0)
     (HGET1:Some mb2 = Ir.Memory.get (Ir.Config.m st) b1)
     (HNONDET:Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog b0 n0) 
          (Ir.plog b1 n1) (Ir.Config.m st) = false)
     (HPP: physicalized_ptr (Ir.Config.m st) (Ir.ptr (Ir.plog b0 n0))
          (Ir.ptr (Ir.pphy n l o))),
  Ir.SmallStep.icmp_ule_ptr (Ir.pphy n l o) (Ir.plog b1 n1) (Ir.Config.m st) =
  Ir.SmallStep.icmp_ule_ptr (Ir.plog b0 n0) (Ir.plog b1 n1) (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr in *.
  rewrite HNONDET. rewrite <- HGET1.
  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET.
  destruct (b0 =? b1) eqn:HEQ; try ss.
  rewrite Nat.eqb_eq in HEQ. subst b1.
  rewrite <- HGET0 in HGET1. inv HGET1.
  rewrite <- HGET0 in HNONDET.
  unfold Ir.log_to_phy.
  rewrite <- HGET0.
  rewrite Nat.min_id.
  rewrite twos_compl_MEMSZ_PTRSZ.
  eapply physicalized_ptr_convert in HPP; try reflexivity; try eassumption.
  assert (Ir.MemBlock.inbounds n0 mb2 = true).
  { unfold Ir.MemBlock.inbounds. rewrite orb_false_iff in HNONDET.
    destruct HNONDET. rewrite negb_false_iff in H. assumption. }
  assert (Ir.MemBlock.inbounds n1 mb2 = true).
  { unfold Ir.MemBlock.inbounds. rewrite orb_false_iff in HNONDET.
    destruct HNONDET. rewrite negb_false_iff in H1. assumption. }

  rewrite Ir.MemBlock.inbounds_mod; try assumption.
  rewrite Ir.MemBlock.inbounds_mod in HPP; try assumption.
  rewrite <- HPP.
  rewrite leb_add. reflexivity.
  { inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in HGET0.
    eassumption. reflexivity. }
  { inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in HGET0.
    eassumption. reflexivity. }
Qed.

Lemma phy_p2N:
  forall md st o I s op
         (HWF:Ir.Config.wf md st)
         (HOP:Some (Ir.ptr (Ir.pphy o I s)) = Ir.Config.get_val st op),
    Ir.SmallStep.p2N (Ir.pphy o I s) (Ir.Config.m st) Ir.PTRSZ = o.
Proof.
  intros.
  unfold Ir.SmallStep.p2N.
  rewrite Nat.min_id.
  unfold Ir.SmallStep.twos_compl.
  rewrite PTRSZ_MEMSZ.
  apply Nat.mod_small.
  inv HWF.
  symmetry in HOP. eapply phy_ofs_lt_MEMSZ; eauto.
Qed.


Theorem icmp_ule_refines_l:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr11 opptr12 opptr2 ptrty v1 v2 sr2
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
         (* And.. have a step. *)
         (* Note that icmp has nondet. semantics, so we should use
            exists quantifier. *)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    exists sr1,
         Ir.SmallStep.sstep md1 st sr1 /\
         Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP2.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST2 in HNEXT.
      rewrite HOP2 in HNEXT.
      dup HPP. dup HPP.
      eapply physicalized_ptr_valty in HPP.
      inv HPP.
      { (* poison, poison *)
        inv H. inv HNEXT.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite <- HINST1. rewrite HOP1. reflexivity. }
        { constructor. constructor. thats_it. }
      }
      inv H.
      { (* poison, ptr *)
        inv H0. inv H1.
        des_ifs;
        ( eexists; split;
          [ eapply Ir.SmallStep.ss_inst; eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite <- HINST1; rewrite HOP1; reflexivity
          | constructor; constructor; thats_it ]
        ).
      }
      { (* ptr, ptr *)
        inv H0. inv H. inv H1.
        des_ifs.
        { eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { constructor. constructor. thats_it. }
        }
        { destruct x0.
          { (* x0 cannot be log *)
            eapply physicalized_ptr_nonlog in HPP0. exfalso.
            eapply HPP0. eexists. eexists. reflexivity. }
          (* destructing opptr11.. *)
          destruct x.
          {
            inv HWF1.
            dup HOP1. apply wf_ptr in HOP0. inv HOP0. exploit H. ss.
            intros HH. inv HH. inv H2.

            destruct p.
            { (* src: icmp ule log, log
                 tgt: icmp ule phy, log *)
              destruct (Ir.SmallStep.icmp_ule_ptr_nondet_cond
                          (Ir.plog b0 n0) (Ir.plog b1 n1) (Ir.Config.m st)) eqn:HNONDET.
              { (* nondet. *)
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_icmp_ule_nondet.
                  eassumption. reflexivity.
                  rewrite HOP1. reflexivity.
                  rewrite Heq. reflexivity.
                  assumption.
                }
                { constructor. constructor.
                  thats_it. }
              }
              { dup Heq. apply wf_ptr in Heq1. inv Heq1. exploit H2. ss.
                intros HH. inv HH. inv H6.
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                  unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                  rewrite HOP1. rewrite Heq.
                  erewrite physicalized_ptr_icmp_ule_nondet in Heq0.
                  { rewrite Heq0. reflexivity. }
                  { eassumption. }
                  { eauto. }
                  { eauto. }
                  { assumption. }
                  { assumption. }
                }
                { cc_thats_it. }
              }
            }
            { (* src: icmp ule log, phy
                 tgt: icmp ule phy, phy *)
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                rewrite HOP1. rewrite Heq.
                assert (HPTR:
                          Ir.SmallStep.icmp_ule_ptr (Ir.pphy n l o)
                                                    (Ir.pphy n1 l0 o0) (Ir.Config.m st) =
                          Ir.SmallStep.icmp_ule_ptr (Ir.plog b0 n0)
                                                    (Ir.pphy n1 l0 o0) (Ir.Config.m st)).
                { unfold Ir.SmallStep.icmp_ule_ptr.
                  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
                  erewrite p2N_addr. 2: eauto.
                  erewrite phy_p2N; try eassumption.
                  eapply physicalized_ptr_convert in HPP0; try reflexivity.
                  rewrite <- HPP0. reflexivity.
                  congruence. rewrite Heq. reflexivity.
                }
                rewrite HPTR in Heq0.
                rewrite Heq0. reflexivity.
              }
              { cc_thats_it. }
            }
          }
          { (* all physical! *)
            eapply physicalized_ptr_phy in HPP0; try reflexivity.
            inv HPP0. inv H0.
            eexists. split.
            { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
              rewrite HOP1. rewrite Heq.
              unfold Ir.SmallStep.icmp_ule_ptr in *.
              des_ifs.
            }
            { unfold Ir.SmallStep.icmp_ule_ptr in Heq0.
              des_ifs.
              cc_thats_it. }
          }
        }
        { (* opptr2 is poison. *)
          eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { cc_thats_it. }
        }
        { (* opptr2 is None. -_-; *)
          eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { cc_thats_it. }
        }
      }
      { inv HWF1. assumption. }
    }
    { rewrite <- HINST2 in HCUR. inv HCUR.
      (* cannot be nondeterministic chocie. due to existence of phy *)
      dup HPP.
      eapply physicalized_ptr_valty in HPP; try reflexivity.
      inv HPP.
      { inv H. congruence. }
      inv H.
      { inv H0. inv H1. rewrite HOP2 in HOP0. inv HOP0.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
          rewrite HOP1. reflexivity. }
        { cc_thats_it. }
      }
      { inv H0. inv H. inv H1.
        rewrite HOP2 in HOP0. inv HOP0.
        eapply physicalized_ptr_nonlog in HPP0.
        unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET.
        des_ifs; exfalso; eapply HPP0; do 2 eexists; reflexivity.
      }
      { inv HWF1. assumption. }
    }
  }
  { hey_terminator HINST2. }
  { hey_terminator2 HINST2 HTSTEP. }
Qed.


Lemma physicalized_ptr_icmp_ule_nondet2:
  forall md st b0 b1 mb1 mb2 n0 n1 n l o
     (HWF:Ir.Config.wf md st)
     (HGET1:Some mb1 = Ir.Memory.get (Ir.Config.m st) b0)
     (HGET1:Some mb2 = Ir.Memory.get (Ir.Config.m st) b1)
     (HNONDET:Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog b0 n0) 
          (Ir.plog b1 n1) (Ir.Config.m st) = false)
     (HPP: physicalized_ptr (Ir.Config.m st) (Ir.ptr (Ir.plog b1 n1))
          (Ir.ptr (Ir.pphy n l o))),
  Ir.SmallStep.icmp_ule_ptr (Ir.plog b0 n0) (Ir.pphy n l o) (Ir.Config.m st) =
  Ir.SmallStep.icmp_ule_ptr (Ir.plog b0 n0) (Ir.plog b1 n1) (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.SmallStep.icmp_ule_ptr in *.
  rewrite HNONDET. rewrite <- HGET1.
  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET.
  destruct (b0 =? b1) eqn:HEQ; try ss.
  rewrite Nat.eqb_eq in HEQ. subst b1.
  rewrite <- HGET0 in HGET1. inv HGET1.
  rewrite <- HGET0 in HNONDET.
  unfold Ir.log_to_phy.
  rewrite <- HGET0.
  rewrite Nat.min_id.
  rewrite twos_compl_MEMSZ_PTRSZ.
  eapply physicalized_ptr_convert in HPP; try reflexivity; try eassumption.
  assert (Ir.MemBlock.inbounds n0 mb2 = true).
  { unfold Ir.MemBlock.inbounds. rewrite orb_false_iff in HNONDET.
    destruct HNONDET. rewrite negb_false_iff in H. assumption. }
  assert (Ir.MemBlock.inbounds n1 mb2 = true).
  { unfold Ir.MemBlock.inbounds. rewrite orb_false_iff in HNONDET.
    destruct HNONDET. rewrite negb_false_iff in H1. assumption. }

  rewrite Ir.MemBlock.inbounds_mod; try assumption.
  rewrite Ir.MemBlock.inbounds_mod in HPP; try assumption.
  rewrite <- HPP.
  rewrite leb_add. reflexivity.
  { inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in HGET0.
    eassumption. reflexivity. }
  { inv HWF. inv wf_m. eapply wf_blocks. eapply Ir.Memory.get_In in HGET0.
    eassumption. reflexivity. }
Qed.

Theorem icmp_ule_refines_r:
  forall md1 md2 (* md2 is an optimized program *)
         st r opptr1 opptr21 opptr22 ptrty v1 v2 sr2
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
         (HPP:physicalized_ptr (Ir.Config.m st) v1 v2)
         (* And.. have a step. *)
         (* Note that icmp has nondet. semantics, so we should use
            exists quantifier. *)
         (HSTEP2:Ir.SmallStep.sstep md2 st sr2),
    exists sr1,
         Ir.SmallStep.sstep md1 st sr1 /\
         Ir.Refinement.refines_step_res sr2 sr1. (* target refines source *)
Proof.
  intros.
  inv HSTEP2.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST2 in HNEXT.
      rewrite HOP2 in HNEXT.
      dup HPP. dup HPP.
      eapply physicalized_ptr_valty in HPP.
      inv HPP.
      { (* poison, poison *)
        inv H. inv HNEXT.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step.
          rewrite <- HINST1. rewrite HOP1. des_ifs; reflexivity. }
        { des_ifs; cc_thats_it. }
      }
      inv H.
      { (* poison, ptr *)
        inv H0. inv H1.
        des_ifs;
        ( eexists; split;
          [ eapply Ir.SmallStep.ss_inst; eapply Ir.SmallStep.s_det;
            unfold Ir.SmallStep.inst_det_step;
            rewrite <- HINST1; rewrite HOP1; des_ifs; reflexivity
          | des_ifs; cc_thats_it ]
        ).
      }
      { (* ptr, ptr *)
        inv H0. inv H. inv H1.
        des_ifs.
        { eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { constructor. constructor. thats_it. }
        }
        { destruct x0.
          { (* x0 cannot be log *)
            eapply physicalized_ptr_nonlog in HPP0. exfalso.
            eapply HPP0. eexists. eexists. reflexivity. }
          (* destructing opptr21.. *)
          destruct x.
          {
            inv HWF1.
            dup HOP1. apply wf_ptr in HOP0. inv HOP0. exploit H. ss.
            intros HH. inv HH. inv H2.

            destruct p.
            { (* src: icmp ule log, log
                 tgt: icmp ule log, phy *)
              destruct (Ir.SmallStep.icmp_ule_ptr_nondet_cond
                          (Ir.plog b1 n1) (Ir.plog b0 n0) (Ir.Config.m st)) eqn:HNONDET.
              { (* nondet. *)
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_icmp_ule_nondet.
                  eassumption. reflexivity.
                  rewrite Heq. reflexivity.
                  rewrite HOP1. reflexivity.
                  assumption.
                }
                { constructor. constructor.
                  thats_it. }
              }
              { dup Heq. apply wf_ptr in Heq1. inv Heq1. exploit H2. ss. intros HH.
                inv HH. inv H6.
                eexists. split.
                { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                  unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                  rewrite HOP1. rewrite Heq.
                  erewrite physicalized_ptr_icmp_ule_nondet2 in Heq0.
                  { rewrite Heq0. reflexivity. }
                  { eassumption. }
                  { eauto. }
                  { eauto. }
                  { assumption. }
                  { assumption. }
                }
                { cc_thats_it. }
              }
            }
            { (* src: icmp ule phy, log
                 tgt: icmp ule phy, phy *)
              eexists. split.
              { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
                unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
                rewrite HOP1. rewrite Heq.
                assert (HPTR:
                          Ir.SmallStep.icmp_ule_ptr (Ir.pphy n1 l0 o0)
                                                    (Ir.pphy n l o) (Ir.Config.m st) =
                          Ir.SmallStep.icmp_ule_ptr (Ir.pphy n1 l0 o0)
                                                    (Ir.plog b0 n0) (Ir.Config.m st)).
                { unfold Ir.SmallStep.icmp_ule_ptr.
                  unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
                  erewrite p2N_addr. 2: eauto.
                  erewrite phy_p2N; try eassumption.
                  eapply physicalized_ptr_convert in HPP0; try reflexivity.
                  rewrite <- HPP0. reflexivity.
                  congruence. rewrite HOP2. reflexivity.
                }
                rewrite HPTR in Heq0.
                rewrite Heq0. reflexivity.
              }
              { cc_thats_it. }
            }
          }
          { (* opptr21, opptr22 all physical! *)
            eapply physicalized_ptr_phy in HPP0; try reflexivity.
            inv HPP0. inv H0.
            eexists. split.
            { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
              unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
              rewrite HOP1. rewrite Heq.
              assert (Ir.SmallStep.icmp_ule_ptr p (Ir.pphy n l0 o0) (Ir.Config.m st) =
                      Ir.SmallStep.icmp_ule_ptr p (Ir.pphy n l None) (Ir.Config.m st)).
              { unfold Ir.SmallStep.icmp_ule_ptr.
                unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
                des_ifs. }
              rewrite H0. rewrite Heq0. reflexivity.
            }
            { cc_thats_it. }
          }
        }
        { (* opptr1 is poison. *)
          eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { cc_thats_it. }
        }
        { (* opptr1 is None. -_-; *)
          eexists. split.
          { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
            unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
            rewrite HOP1. rewrite Heq. reflexivity. }
          { cc_thats_it. }
        }
      }
      { inv HWF1. assumption. }
    }
    { rewrite <- HINST2 in HCUR. inv HCUR.
      (* cannot be nondeterministic chocie. due to existence of phy *)
      dup HPP.
      eapply physicalized_ptr_valty in HPP; try reflexivity.
      inv HPP.
      { inv H. congruence. }
      inv H.
      { inv H0. inv H1. rewrite HOP2 in HOP3. inv HOP3.
        eexists. split.
        { eapply Ir.SmallStep.ss_inst. eapply Ir.SmallStep.s_det.
          unfold Ir.SmallStep.inst_det_step. rewrite <- HINST1.
          rewrite HOP1. des_ifs; reflexivity. }
        { cc_thats_it. }
      }
      { inv H0. inv H. inv H1.
        rewrite HOP2 in HOP3. inv HOP3.
        eapply physicalized_ptr_nonlog in HPP0.
        unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond in HNONDET.
        des_ifs; exfalso; eapply HPP0; do 2 eexists; reflexivity.
      }
      { inv HWF1. assumption. }
    }
  }
  { hey_terminator HINST2. }
  { hey_terminator2 HINST2 HTSTEP. }
Qed.

(*****
      Refinement on getelementptr is not needed because
      physicalized_ptr already contains it. :)
      In the same context refinement on bitcast is also not
      needed because it returns identical value if
      the input is a pointer value.
 *****)


End GVN1.

End Ir.

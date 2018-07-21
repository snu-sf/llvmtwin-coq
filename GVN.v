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
      { des_ifs.
        eexists. eexists . reflexivity. }
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
      des_ifs.
      {
        exploit IHHPP.
        { reflexivity. }
        { reflexivity. }
        intros HH.
        unfold Ir.SmallStep.gep in HP2'.
        des_ifs.
        { inv HH. destruct H0.
          split. reflexivity.
          split. constructor. constructor. assumption.
          assumption.
        }
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        des_ifs.
        split. reflexivity.
        split. constructor. constructor. assumption.
        reflexivity.
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        des_ifs.
      }
    }
  }
Qed.

Lemma physicalized_ptr_log:
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
      des_ifs.
      {
        exploit IHHPP.
        { reflexivity. }
        { reflexivity. }
        { assumption. }
        intros HH.
        unfold Ir.SmallStep.gep in HP2'.
        destruct ((idx * N.of_nat (Ir.ty_bytesz t) <?
            N.shiftl 1 (N.of_nat Ir.PTRSZ - 1))%N) eqn:H11.
        { (* positive offset add *)
          destruct (N.to_nat
             (Ir.SmallStep.twos_compl_add (N.of_nat n)
                (idx * N.of_nat (Ir.ty_bytesz t)) Ir.PTRSZ) <? Ir.MEMSZ) eqn:H2.
          { assert 
        des_ifs.
        { inv HH. destruct H0.
          split. reflexivity.
          split. constructor. constructor. assumption.
          assumption.
        }
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        des_ifs.
        split. reflexivity.
        split. constructor. constructor. assumption.
        reflexivity.
      }
      { exploit IHHPP; try reflexivity.
        intros HH.
        inv HH. destruct H0.
        unfold Ir.SmallStep.gep in HP2'.
        des_ifs.
      }
    }
  }
Qed.

Lemma get_deref_physicalized_ptr:
  forall md st sz p1 p2
         (HWF:Ir.Config.wf md st)
         (HSZ:sz> 0)
         (HPP:physicalized_ptr (Ir.Config.m st) (Ir.ptr p1) (Ir.ptr p2)),
    forall blk, Ir.get_deref (Ir.Config.m st) p1 sz = [blk] ->
                Ir.get_deref (Ir.Config.m st) p2 sz = [blk].
Proof.
  intros.
  inv HWF.
  remember (Ir.ptr p1) as v1.
  remember (Ir.ptr p2) as v2.
  generalize dependent blk.
  generalize dependent p1.
  generalize dependent p2.
  clear wf_cid_to_f.
  clear wf_cid_to_f2.
  clear wf_stack.
  clear wf_no_bogus_ptr.
  clear wf_no_bogus_ptr_mem.
  induction HPP.
  { intros.
    rename p0 into p2'.
    rename p3 into p1'.
    inv Heqv2. inv Heqv1.
    eapply Ir.get_deref_ptr_phy_same.
    { eassumption. }
    { omega. }
    { eassumption. }
    { congruence. }
  }
  { intros.
    subst p2'.
    subst p1'.
    assert (HA := IHHPP wf_m p2 (eq_refl (Ir.ptr p2)) p1 ).
    rename p0 into p2'.
    rename p3 into p1'.
    clear IHHPP.
    unfold Ir.SmallStep.gep in Heqv1.
    destruct p1.
    { (* p1 was log. *)
      destruct inb eqn:HINB.
      { (* inbounds *)
        des_ifs.
        (* okay, how about p2? *)
        unfold Ir.SmallStep.gep in Heqv2.
        destruct p2.
        { admit. }
        { (* p2 is phy. *)
          des_ifs.
          { (* added offset was positive. *)
            eapply Ir.get_deref_ptr_phy_same in H; try assumption.
            2: unfold Ir.ptr_to_phy.
            2: unfold Ir.log_to_phy.
            2: rewrite Heq.
            2: reflexivity.
            (* okay, Ir.plog b n and Ir.pphy (n0 l o) has same integer repr. *)
            
            assert (Ir.get_deref m (Ir.plog b n) sz = [(b, t0, n)]).
            { unfold Ir.get_deref.
              rewrite Heq.
              unfold Ir.get_deref in H.
              rewrite Heq in H.
              destruct (Ir.MemBlock.alive t0).
              { simpl. 
          { (* added offset was negative - no check *)
    
    
    

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

      (* okay.. time to do induction. *)
      clear wf_cid_to_f.
      clear wf_cid_to_f2.
      clear wf_stack.
      clear wf_no_bogus_ptr.
      clear wf_no_bogus_ptr_mem.
      induction HPP.
      { (* base case *)
        unfold Ir.deref in HNEXT.
        destruct (Ir.get_deref m p1 (Ir.ty_bytesz retty)) eqn:HDEREF1.
        { (* source is UB - it's done .*)
          inv HNEXT. constructor. }
        { inv HNEXT.
          dup HDEREF1.
          eapply Ir.get_deref_singleton in HDEREF0; try assumption.
          {
            destruct HDEREF0; try congruence.
            destruct H. destruct H. inv H.
            dup HDEREF1.
            apply Ir.get_deref_ptr_phy_same with (p' := p2) in HDEREF1;
              try assumption.
            {
              unfold Ir.deref in HNEXT0.
              rewrite HDEREF1 in HNEXT0.
              inv HNEXT0.
              unfold Ir.load_val.
              unfold Ir.load_bytes.
              { rewrite HDEREF1. rewrite HDEREF0.
                destruct x. destruct p.
                constructor.
                { constructor. }
                { eapply eq_update_reg_and_incrpc2; try eassumption. }
              }
            }
            { apply Ir.ty_bytesz_pos. }
            { congruence. }
          }
          { apply Ir.ty_bytesz_pos. }
        }
      }
      { (* a bit more complex case *)
        admit.
      }
    }
    { (* okay, br in target went wrong. *)
      (* br in src shoud also go wrong. *)
      apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
      inv HISTEP; try
       (apply Ir.Config.cur_inst_not_cur_terminator in HINST2;
        congruence).
    }
    { apply Ir.Config.cur_inst_not_cur_terminator in HINST2.
      unfold Ir.SmallStep.t_step in HTSTEP.
      rewrite <- HINST2 in HTSTEP.
      congruence.
    }
  }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
    unfold Ir.SmallStep.t_step in HTSTEP.
    rewrite <- HINST1 in HTSTEP.
    congruence. }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST1.
    unfold Ir.SmallStep.t_step in HTSTEP.
    rewrite <- HINST1 in HTSTEP.
    congruence. }
Admitted.
  

End GVN.

End Ir.
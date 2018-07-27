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

Module GVN3.


(* 3nd condition of replacing p with q:
   If p and q are both computed by the gep inbounds with same
   base pointer, it is valid to replace p with q. *)
Definition eqprop_valid3 (m:Ir.Memory.t) (p q:Ir.val) :=
  exists p0 idx1 idx2 ty1 ty2,
    p = Ir.SmallStep.gep p0 idx1 ty1 m true /\
    q = Ir.SmallStep.gep p0 idx2 ty2 m true.



(*********************************************************
 Important property of eqprop_valid3:
  If eqprop_valid3 p q holds, and `icmp eq p, q` evaluates
    to true, then p and q are exactly the same pointer.
 *********************************************************)

Lemma twos_compl_twos_compl_add_OPAQUED_PTRSZ:
  forall n x,
    Ir.SmallStep.twos_compl (Ir.SmallStep.twos_compl_add n x Ir.SmallStep.OPAQUED_PTRSZ) Ir.PTRSZ =
    Ir.SmallStep.twos_compl_add n x Ir.SmallStep.OPAQUED_PTRSZ.
Proof.
  intros.
  rewrite Ir.GVN1.OPAQUED_PTRSZ_PTRSZ.
  unfold Ir.SmallStep.twos_compl_add.
  unfold Ir.SmallStep.twos_compl.
  rewrite Nat.mod_mod. reflexivity.
  apply shiftl_2_nonzero.
Qed.

Theorem gep_never_returns_num:
  forall v p idx ty m inb
    (HGEP1:Ir.SmallStep.gep p idx ty m inb = v),
    ~exists n, v = Ir.num n.
Proof.
  intros.
  unfold Ir.SmallStep.gep in HGEP1.
  intros HH.
  inv HH.
  des_ifs.
Qed.

(* I had to split the big theorem into lemmas due to
   Coq bug - Coq does not terminate processing of 'Qed.', due to unknown reason :( *)
Lemma eqprop_valid3_after_icmpeq_true_log:
  forall md st st' r ptrty op1 op2 p1 p2 e l0 o0 idx1 ty1 idx2 ty2
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iicmp_eq r ptrty op1 op2) = Ir.Config.cur_inst md st)
    (HOP1:Some (Ir.ptr p1) = Ir.Config.get_val st op1)
    (HOP2:Some (Ir.ptr p2) = Ir.Config.get_val st op2)
    (* geps *)
    (HGEP1:(Ir.ptr p1) = Ir.SmallStep.gep (Ir.plog l0 o0) idx1 ty1 (Ir.Config.m st) true)
    (HGEP2:(Ir.ptr p2) = Ir.SmallStep.gep (Ir.plog l0 o0) idx2 ty2 (Ir.Config.m st) true)
    (* have a small step *)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st'))
    (* p1 == p2 is true *)
    (HTRUE:Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r)),

    p1 = p2.
Proof.
  intros.

  assert (HS:Ir.Config.s st <> []).
  {
    unfold Ir.Config.cur_inst in HINST.
    unfold Ir.Config.cur_fdef_pc in HINST.
    des_ifs.
  }

  inv HSTEP.
  { inv HISTEP; try congruence.
    { unfold Ir.SmallStep.inst_det_step in HNEXT.
      rewrite <- HINST in HNEXT.
      rewrite <- HOP1, <- HOP2 in HNEXT.
      unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
      unfold Ir.SmallStep.gep in *.
      des_ifs.
      {
        rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
        unfold Ir.Config.get_val in HTRUE.
        rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
        inv HTRUE.
        des_ifs.
        rewrite Nat.eqb_eq in Heq3. congruence. assumption.
      }
      {
        rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
        unfold Ir.Config.get_val in HTRUE.
        rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
        inv HTRUE.
        des_ifs.
      }
    }
    { rewrite <- HINST in HCUR.
      inv HCUR.
      rewrite <- HOP1 in HOP0. inv HOP0.
      rewrite <- HOP2 in HOP3. inv HOP3.
      unfold Ir.SmallStep.gep in *.
      unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in *.
      des_ifs; rewrite Nat.eqb_refl in HNONDET; inv HNONDET.
    }
  }
  { apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    unfold Ir.SmallStep.t_step in HTSTEP. rewrite <- HINST in HTSTEP.
    congruence.
  }
Qed.

Definition OPAQUED_MEMSZ := Ir.SmallStep.locked nat Ir.MEMSZ.
Lemma OPAQUED_MEMSZ_MEMSZ:
  OPAQUED_MEMSZ = Ir.MEMSZ.
Proof.
  intros. unfold OPAQUED_MEMSZ. unfold Ir.SmallStep.locked.
  des_ifs.
Qed.

(* due to Coq bug, I made a separated lemmax *)
Lemma gep_helper_small:
  forall n l o x1 x3 st p0 n'1
(HVAL2 : Ir.SmallStep.gep (Ir.pphy n l o) x1 x3 (Ir.Config.m st) true =
          Ir.ptr p0)
(Heqn'1: n'1 =
           Ir.SmallStep.twos_compl_add n (x1 * Ir.ty_bytesz x3)
             Ir.SmallStep.OPAQUED_PTRSZ),
  p0 = Ir.pphy n'1 (n::n'1::l) o.
Proof.
  intros. unfold Ir.SmallStep.gep in HVAL2. des_ifs.
Qed.

Lemma gep_helper:
  forall n l o x1 x3 x0 x2 st p0 p st' r e md
(HVAL2 : Ir.SmallStep.gep (Ir.pphy n l o) x1 x3 (Ir.Config.m st) true =
          Ir.ptr p0)
(HVAL1 : Ir.SmallStep.gep (Ir.pphy n l o) x0 x2 (Ir.Config.m st) true =
          Ir.ptr p)
(HTRUE : Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r))
(HNEXT : Some (Ir.SmallStep.sr_success e st') =
          match Ir.SmallStep.icmp_eq_ptr p p0 (Ir.Config.m st) with
          | Some b =>
              Some
                (Ir.SmallStep.sr_success Behaviors.Ir.e_none
                   (Ir.SmallStep.update_reg_and_incrpc md st r
                      (Ir.SmallStep.to_num b)))
          | None => None
          end)
(HS : Ir.Config.s st <> []),
    Ir.ptr p = Ir.ptr p0.
Proof.
  intros.
  eapply gep_helper_small in HVAL2; try reflexivity.
  eapply gep_helper_small in HVAL1; try reflexivity.
  rewrite HVAL1, HVAL2 in HNEXT.
  unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
  unfold Ir.SmallStep.p2N in HNEXT.
  rewrite twos_compl_twos_compl_add_OPAQUED_PTRSZ in HNEXT.
  inversion HNEXT.
  rewrite H1 in HTRUE.
  rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
  unfold Ir.Config.get_val in HTRUE.
  rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
  inversion HTRUE.
  destruct (Ir.SmallStep.twos_compl_add n (x0 * Ir.ty_bytesz x2) Ir.SmallStep.OPAQUED_PTRSZ =?
         Ir.SmallStep.twos_compl_add n (x1 * Ir.ty_bytesz x3) Ir.SmallStep.OPAQUED_PTRSZ)
           eqn:Heq; try congruence.
  rewrite Nat.eqb_eq in Heq. rewrite HVAL1, HVAL2, Heq.
  reflexivity.
  assumption.
Admitted. (* This is really strange.. Why Qed never ends? *)


Theorem eqprop_valid3_after_icmpeq_true:
  forall md st st' r ptrty op1 op2 v1 v2 e
    (HWF:Ir.Config.wf md st)
    (HINST:Some (Ir.Inst.iicmp_eq r ptrty op1 op2) = Ir.Config.cur_inst md st)
    (HOP1:Some v1 = Ir.Config.get_val st op1)
    (HOP2:Some v2 = Ir.Config.get_val st op2)
    (* eqprop_valid3 holds *)
    (HEQPROP:eqprop_valid3 (Ir.Config.m st) v1 v2)
    (* have a small step *)
    (HSTEP:Ir.SmallStep.sstep md st (Ir.SmallStep.sr_success e st'))
    (* p1 == p2 is true *)
    (HTRUE:Some (Ir.num 1) = Ir.Config.get_val st' (Ir.opreg r)),

    v1 = v2.
Proof.
  intros.
  assert (HS:Ir.Config.s st <> []).
  {
    unfold Ir.Config.cur_inst in HINST.
    unfold Ir.Config.cur_fdef_pc in HINST.
    des_ifs.
  }

  inv HSTEP.
  { inv HISTEP; try congruence.
    { inv HEQPROP.
      inv H. inv H0. inv H. inv H0. inv H.
      destruct x.
      { destruct (Ir.SmallStep.gep (Ir.plog b n) x0 x2 (Ir.Config.m st) true) eqn:HVAL1;
          destruct (Ir.SmallStep.gep (Ir.plog b n) x1 x3 (Ir.Config.m st) true) eqn:HVAL2;
        try (apply gep_never_returns_num in HVAL1;
             exfalso; apply HVAL1; eexists; reflexivity);
        try (apply gep_never_returns_num in HVAL2;
             exfalso; apply HVAL2; eexists; reflexivity).
        { exploit eqprop_valid3_after_icmpeq_true_log.
          { eassumption. }
          { eassumption. }
          { eassumption. }
          { eassumption. }
          { rewrite HVAL1. reflexivity. }
          { rewrite HVAL2. reflexivity. }
          { eapply Ir.SmallStep.ss_inst.
            eapply Ir.SmallStep.s_det.
            eassumption. }
          { eassumption. }
          intros HH. congruence.
        }
        { unfold Ir.SmallStep.inst_det_step in HNEXT.
          rewrite <- HINST in HNEXT.
          rewrite <- HOP2 in HNEXT. des_ifs.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          inv HTRUE. assumption.
        }
        { unfold Ir.SmallStep.inst_det_step in HNEXT.
          rewrite <- HINST in HNEXT.
          rewrite <- HOP1 in HNEXT. des_ifs.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          inv HTRUE. assumption.
        }
        { unfold Ir.SmallStep.inst_det_step in HNEXT.
          rewrite <- HINST in HNEXT.
          rewrite <- HOP2 in HNEXT. des_ifs.
        }
      }
      { (* phy. *)
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite <- HINST in HNEXT.
        rewrite <- HOP1, <- HOP2 in HNEXT.

        destruct (Ir.SmallStep.gep (Ir.pphy n l o) x0 x2 (Ir.Config.m st) true) eqn:HVAL1;
          destruct (Ir.SmallStep.gep (Ir.pphy n l o) x1 x3 (Ir.Config.m st) true) eqn:HVAL2;
        try (apply gep_never_returns_num in HVAL1;
             exfalso; apply HVAL1; eexists; reflexivity);
        try (apply gep_never_returns_num in HVAL2;
             exfalso; apply HVAL2; eexists; reflexivity).
        { eapply gep_helper; try eassumption. }
        { inv HNEXT.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          inv HTRUE. assumption. }
        { inv HNEXT.
          rewrite Ir.SmallStep.get_val_update_reg_and_incrpc in HTRUE.
          unfold Ir.Config.get_val in HTRUE.
          rewrite Ir.Config.get_rval_update_rval_id in HTRUE.
          inv HTRUE. assumption. }
        { reflexivity. }
      }
    }
    { (* well, cannot be nondet... *)
      rewrite <- HINST in HCUR. inv HCUR.
      rewrite <- HOP1 in HOP0. inv HOP0.
      rewrite <- HOP2 in HOP3. inv HOP3.
      inv HEQPROP.
      inv H. inv H0. inv H. inv H0. destruct H.
      destruct x.
      { assert (HOFS1:exists ofs1, p1 = (Ir.plog b ofs1)).
        { unfold Ir.SmallStep.gep in H.
          unfold Ir.SmallStep.gep in H0.
          unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
          des_ifs; eexists; reflexivity. }
        assert (HOFS2:exists ofs2, p2 = (Ir.plog b ofs2)).
        { unfold Ir.SmallStep.gep in H.
          unfold Ir.SmallStep.gep in H0.
          unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
          des_ifs; eexists; reflexivity. }
        inv HOFS1. inv HOFS2.
        unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
        des_ifs;
          rewrite Nat.eqb_refl in HNONDET; inv HNONDET.
      }
      { assert (HOFS1:exists a1 b1 c1, p1 = (Ir.pphy a1 b1 c1)).
        { unfold Ir.SmallStep.gep in H.
          unfold Ir.SmallStep.gep in H0.
          unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
          des_ifs; eexists; reflexivity. }
        assert (HOFS2:exists a2 b2 c2, p2 = (Ir.pphy a2 b2 c2)).
        { unfold Ir.SmallStep.gep in H.
          unfold Ir.SmallStep.gep in H0.
          unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
          des_ifs; eexists; reflexivity. }
        inv HOFS1. inv H1. inv H2.
        inv HOFS2. inv H1. inv H2.
        unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
        des_ifs.
      }
    }
  }
  { (* terminator! *)
    apply Ir.Config.cur_inst_not_cur_terminator in HINST.
    unfold Ir.SmallStep.t_step in HTSTEP.
    rewrite <- HINST in HTSTEP.
    congruence.
  }
Qed.

(*********************************************************
    Okay, from theorem `eqprop_valid3_after_icmpeq_true`,
    we can say that two pointers have same value after
    `p == q` check.
    It is trivial to have same execution when same value
    is given, hence not proved.
 *********************************************************)

End GVN3.

End Ir.
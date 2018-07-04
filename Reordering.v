Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.

Require Import Common.
Require Import Lang.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import Behaviors.

Module Ir.

Module Reordering.

(* Checks whether instruction i2 has data dependency on instruction i1.
   There's no data dependency, reordering 'i1;i2' into 'i2;i1' wouldn't break use-def chain.
   Note that this function does not check whether bi2 dominates i1.
   If i1 has no def (e.g. store instruction), this returns false. *)
Definition has_data_dependency (i1 i2:Ir.Inst.t): bool :=
  match (Ir.Inst.def i1) with
  | None => false
  | Some (r1, _) => (List.existsb (fun r => Nat.eqb r r1) (Ir.Inst.regops i2))
  end.

(* Analogous to Ir.SmallStep.incrpc, except that it returns None if there's no
   trivial next pc. *)
Definition incrpc' (md:Ir.IRModule.t) (c:Ir.Config.t):option Ir.Config.t :=
  match (Ir.Config.cur_fdef_pc md c) with
  | Some (fdef, pc0) =>
    match (Ir.IRFunction.next_trivial_pc pc0 fdef) with
    | Some pc' =>
      Some (Ir.Config.update_pc c pc')
    | None => None (* Cannot happen..! *)
    end
  | None => None (* Cannot happen *)
  end.

(* This proposition holds iff current pc points to i1,
   and the next pc points to i2. *)
Definition inst_locates_at (md:Ir.IRModule.t) (c:Ir.Config.t) (i1 i2:Ir.Inst.t):Prop :=
  exists c',
    Ir.Config.cur_inst md c = Some i1 /\
    Some c' = incrpc' md c /\
    Ir.Config.cur_inst md c' = Some i2.

(* This proposition holds iff (current pc of c1 points to an instruction) <->
   (current pc of c2 points to an instruction. *)
Definition both_inst_or_not (md1 md2:Ir.IRModule.t) (c1 c2:Ir.Config.t):Prop :=
  (exists i1 i2, Ir.Config.cur_inst md1 c1 = Some i1 /\ Ir.Config.cur_inst md2 c2 = Some i2)
    \/
  (Ir.Config.cur_inst md1 c1 = None /\ Ir.Config.cur_inst md2 c2 = None).



Lemma incrpc_update_rval:
  forall md st r v,
    Ir.SmallStep.incrpc md (Ir.Config.update_rval st r v) =
    Ir.Config.update_rval (Ir.SmallStep.incrpc md st) r v.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  des_ifs.
  unfold Ir.Config.update_rval.
  destruct (Ir.Config.s st) eqn:Hs.
  - unfold Ir.Config.update_pc at 2. repeat (rewrite Hs). reflexivity.
  - unfold Ir.Config.update_pc at 2. repeat (rewrite Hs).
    destruct p1 eqn:Hp1.
    destruct p2 eqn:Hp2.
    simpl. unfold Ir.Config.update_pc at 1. simpl.
    unfold Ir.Config.update_pc. repeat (rewrite Hs). simpl.
    reflexivity.
Qed.

Lemma cur_inst_update_reg_and_incrpc:
  forall md st r v,
    Ir.Config.cur_inst md (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.cur_inst md (Ir.SmallStep.incrpc md st).
Proof.
  intros.
  unfold Ir.Config.cur_inst.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite incrpc_update_rval.
  rewrite Ir.Config.cur_fdef_pc_update_rval.
  reflexivity.
Qed.

Lemma incrpc'_incrpc:
  forall md st st'
         (HINCRPC':Some st' = incrpc' md st),
    st' = Ir.SmallStep.incrpc md st.
Proof.
  intros.
  unfold incrpc' in *.
  unfold Ir.SmallStep.incrpc.
  des_ifs.
Qed.

Lemma m_update_reg_and_incrpc:
  forall md st r v,
    Ir.Config.m (Ir.SmallStep.update_reg_and_incrpc md st r v) =
    Ir.Config.m st.
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.update_pc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

Lemma get_val_incrpc:
  forall md st op,
    Ir.Config.get_val (Ir.SmallStep.incrpc md st) op = Ir.Config.get_val st op.
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.get_val.
  des_ifs.
  unfold Ir.Config.update_pc.
  des_ifs.
  unfold Ir.Config.get_rval.
  simpl. rewrite Heq1. reflexivity.
Qed.

Lemma get_val_independent:
  forall r1 r2 (HNEQ:r1 <> r2) md st v,
    Ir.Config.get_val (Ir.SmallStep.update_reg_and_incrpc md st r2 v) (Ir.opreg r1) =
    Ir.Config.get_val st (Ir.opreg r1).
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  rewrite get_val_incrpc.
  unfold Ir.Config.get_val.
  unfold Ir.Config.update_rval.
  unfold Ir.Config.get_rval.
  des_ifs.
  congruence. simpl in Heq. inv Heq.
  unfold Ir.Regfile.update. unfold Ir.Regfile.get.
  simpl. apply not_eq_sym in HNEQ. rewrite <- PeanoNat.Nat.eqb_neq in HNEQ.
  rewrite HNEQ. reflexivity.
Qed.

Lemma config_eq_incrpc:
  forall st1 st2 md1 md2 i1 i2
         (HEQ:Ir.Config.eq st1 st2)
         (HCUR1:Ir.Config.cur_inst md1 st1 = Some i1)
         (HCUR2:Ir.Config.cur_inst md2 st2 = Some i2)
         (HBOTHI:both_inst_or_not md1 md2 (Ir.SmallStep.incrpc md1 st1)
                                  (Ir.SmallStep.incrpc md2 st2)),
    Ir.Config.eq
      (Ir.SmallStep.incrpc md1 st1)
      (Ir.SmallStep.incrpc md2 st2).
Proof.
  intros.
  unfold Ir.SmallStep.incrpc.
  des_ifs.
  (* Show that p = p1.
     next_trivial_pc p0 t = Some p,
     next_trivial_pc p2 t0 = Some p1.
     Show that p0, p2 is the same. *)
  assert (HPP: p0 = p2).
  { unfold Ir.Config.eq in HEQ.
    desH HEQ.
    unfold Ir.Config.cur_fdef_pc in *.
    des_ifs.
    unfold Ir.Stack.eq in HEQ0.
    inv HEQ0. simpl in H2. desH H2. congruence. }
  (* Now show p = p1. *)
  assert (HPP': p = p1).
  { unfold Ir.IRFunction.next_trivial_pc in *.
    unfold both_inst_or_not in HBOTHI.
    unfold Ir.Config.cur_inst in *.
    desH HBOTHI.
    - des_ifs.
      + (* High-level idea:
         Heq4 says # of insts in t1 <= 1 + iidx, but
         Heq5 says # of insts in t2  > 1 + iidx
         *)
        unfold Ir.IRFunction.get_inst in HBOTHI0.
        des_ifs.
        unfold Ir.SmallStep.incrpc in Heq0.
        rewrite Heq7 in Heq0.
        unfold Ir.IRFunction.next_trivial_pc in Heq0.
        rewrite Heq3 in Heq0.
        rewrite Heq4 in Heq0.
        erewrite Ir.Config.cur_fdef_pc_update_pc with (fdef := t0) in Heq0
          by eassumption.
        congruence.
      + unfold Ir.IRFunction.get_inst in HBOTHI.
        des_ifs.
        unfold Ir.SmallStep.incrpc in Heq6.
        rewrite Heq1 in Heq6.
        unfold Ir.IRFunction.next_trivial_pc in Heq6.
        rewrite Heq2 in Heq6.
        rewrite Heq5 in Heq6.
        erewrite Ir.Config.cur_fdef_pc_update_pc with (fdef := t) in Heq6 by eassumption.
        congruence.
    - unfold Ir.SmallStep.incrpc in HBOTHI, HBOTHI0.
      rewrite Heq in HBOTHI.
      rewrite Heq1 in HBOTHI0.
      unfold Ir.IRFunction.next_trivial_pc in HBOTHI, HBOTHI0.
      des_ifs;
      try
        (rewrite Ir.Config.cur_fdef_pc_update_pc with (fdef := t) (p0 := Ir.IRFunction.pc_inst bbid iidx) in Heq6 by assumption;
        inv Heq6;
        unfold Ir.IRFunction.get_inst in HBOTHI;
        rewrite Heq2 in HBOTHI;
        rewrite PeanoNat.Nat.ltb_antisym in HBOTHI;
        simpl in Heq5;
        rewrite Heq5 in HBOTHI;
        simpl in HBOTHI; congruence).
      + admit.
(*      unfold Ir.Config.cur_inst in HBOTHI, HBOTHI0.
      des_ifs.
      unfold Ir.Config.cur_fdef_pc in Heq1.
      unfold Ir.Config.cur_fdef_pc in Heq6.
      des_ifs.
      
      unfold Ir.IRFunction.get_inst in HBOTHI0.
      unfold Ir.IRFunction.get_inst in HCUR2.
      rewrite Heq3 in HCUR2.
      unfold Ir.SmallStep.incrpc in Heq0.
      rewrite Heq7 in Heq0.
      des_ifs.
      
      rewrite PeanoNat.Nat.ltb_antisym in HCUR2.
      
      unfold Ir.SmallStep.incrpc in HBOTHI, HBOTHI0.
      rewrite Heq1 in HBOTHI. rewrite Heq0 in HBOTHI0.
      unfold Ir.IRFunction.next_trivial_pc in HBOTHI, HBOTHI0.
      rewrite Heq2 in HBOTHI.
      rewrite Heq3 in HBOTHI0.
      rewrite Heq5 in HBOTHI.
      rewrite Heq4 in HBOTHI0.
      rewrite Ir.Config.cur_fdef_pc_update_pc
        with (fdef := t0) (p0 := Ir.IRFunction.pc_inst bbid iidx) in HBOTHI0
        by assumption.
      unfold Ir.IRFunction.get_inst in HBOTHI0.
      congruence.
    - unfold 
      + unfold Ir.Config.cur_inst in HBOTHI, HBOTHI0.
        unfold Ir.SmallStep.incrpc in HBOTHI, HBOTHI0.
        rewrite Heq1 in HBOTHI. rewrite Heq0 in HBOTHI0.
        unfold Ir.IRFunction.next_trivial_pc in HBOTHI, HBOTHI0.
        rewrite Heq2 in HBOTHI.
        rewrite Heq3 in HBOTHI0.
        rewrite Heq5 in HBOTHI.
        rewrite Heq4 in HBOTHI0.
        rewrite Ir.Config.cur_fdef_pc_update_pc
          with (fdef := t) (p0 := Ir.IRFunction.pc_inst bbid iidx) in HBOTHI
          by assumption.
        unfold Ir.IRFunction.get_inst in HBOTHI.
        rewrite Heq2 in HBOTHI.
        rewrite PeanoNat.Nat.ltb_antisym in HBOTHI.
        rewrite Heq5 in HBOTHI.
        simpl in HBOTHI.
        congruence.
    - 
  }
  admit.*)
Admitted.

(*
  unfold Ir.Config.eq in HEQ.
  desH HEQ.
  unfold Ir.SmallStep.incrpc.
  unfold Ir.Config.cur_fdef_pc.
  unfold Ir.Config.update_pc.
  des_ifs; simpl in *.
  - unfold Ir.IRFunction.
    split; simpl. assumption.
    split. 
  - rewrite Ir.Config.cur_fdef_pc_eq with (c2 := st2) in Heq by assumption.
    rewrite Heq in Heq1. inv Heq1. rewrite Heq0 in Heq2. inv Heq2.
    apply Ir.Config.eq_update_pc.
    assumption.
  - rewrite Ir.Config.cur_fdef_pc_eq with (c2 := st2) in Heq by assumption.
    rewrite Heq in Heq1. inv Heq1. rewrite Heq0 in Heq2. inv Heq2.
  - rewrite Ir.Config.cur_fdef_pc_eq with (c2 := st2) in Heq by assumption.
    rewrite Heq in Heq1. inv Heq1.
  - rewrite Ir.Config.cur_fdef_pc_eq with (c2 := st2) in Heq by assumption.
    rewrite Heq in Heq1. inv Heq1. rewrite Heq0 in Heq2. inv Heq2.
  - rewrite Ir.Config.cur_fdef_pc_eq with (c2 := st2) in Heq by assumption.
    rewrite Heq in Heq0. inv Heq0.
Qed.
*)
Lemma config_eq_update_reg_and_incrpc:
  forall md st r1 r2 v1 v2
         (HNEQ:r2 <> r1),
    Ir.Config.eq
      (Ir.SmallStep.update_reg_and_incrpc md
        (Ir.SmallStep.update_reg_and_incrpc md st r1 v1) r2 v2)
      (Ir.SmallStep.update_reg_and_incrpc md
        (Ir.SmallStep.update_reg_and_incrpc md st r2 v2) r1 v1).
Proof.
  intros.
  unfold Ir.SmallStep.update_reg_and_incrpc.
  apply config_eq_incrpc.
  rewrite <- incrpc_update_rval.
  rewrite <- incrpc_update_rval.
  apply config_eq_incrpc.
  split.
  { unfold Ir.Config.update_rval. des_ifs. }
  split.
  { unfold Ir.Config.update_rval. des_ifs; simpl in *.
    - rewrite Heq1. constructor.
    - inv Heq. inv Heq1.
      unfold Ir.Regfile.update.
      unfold Ir.Stack.eq.
      constructor.
      + simpl. split. reflexivity. split. reflexivity.
        unfold Ir.Regfile.eq.
        intros.
        unfold Ir.Regfile.get.
        simpl.
        des_ifs; try congruence.
        * rewrite PeanoNat.Nat.eqb_eq in *.
          congruence.
      + clear Heq0.
        induction t3. constructor. constructor.
        split. reflexivity. split. reflexivity. apply Ir.Regfile.eq_refl.
        apply IHt3.
  }
  split.
  { unfold Ir.Config.update_rval.
    unfold Ir.Config.cid_to_f. des_ifs.
  }
  { unfold Ir.Config.update_rval.
    unfold Ir.Config.cid_fresh. des_ifs.
  }
Qed.


Inductive nstep_eq: (Ir.trace * Ir.SmallStep.step_res) ->
                    (Ir.trace * Ir.SmallStep.step_res) -> Prop :=
| nseq_goes_wrong:
    forall (t1 t2:Ir.trace)
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_goes_wrong)) (t2, (Ir.SmallStep.sr_goes_wrong))
| nseq_oom:
    forall (t1 t2:Ir.trace)
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_oom)) (t2, (Ir.SmallStep.sr_oom))
| nseq_prog_finish:
    forall (t1 t2:Ir.trace) v
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2),
      nstep_eq (t1, (Ir.SmallStep.sr_prog_finish v)) (t2, (Ir.SmallStep.sr_prog_finish v))
| nseq_success:
    forall (t1 t2:Ir.trace) e c1 c2
        (HEQ:List.filter Ir.not_none t1 = List.filter Ir.not_none t2)
        (HCEQ:Ir.Config.eq c1 c2),
      nstep_eq (t1, (Ir.SmallStep.sr_success e c1))
               (t2, (Ir.SmallStep.sr_success e c2)).

(* Is it valid to reorder 'i1;i2' into 'i2;i1'? *)
Definition inst_reordering_valid (i1 i2:Ir.Inst.t): Prop :=
  (* If there's no data dependency from i1 to i2 *)
  forall (HNODEP:has_data_dependency i1 i2 = false),
    (* 'i1;i2' -> 'i2;i1' is allowed *)
    forall (md md':Ir.IRModule.t) (* IR Modules *)
           (st:Ir.Config.t) (* Initial state *)
           (HWF:Ir.Config.wf md st) (* Well-formedness of st *)
           (HLOCATE:inst_locates_at md st i1 i2)
           (HLOCATE':inst_locates_at md' st i2 i1)
           (sr:Ir.trace * Ir.SmallStep.step_res)
           (HSTEP:Ir.SmallStep.inst_nstep md st 2 sr),
      exists sr', (* step result after 'i2;i1' *)
        Ir.SmallStep.inst_nstep md' st 2 sr' /\
        nstep_eq sr sr'.


(* If instruction i does not change memory, it does not raise OOM. *)
Lemma no_mem_change_no_oom:
  forall i st md
         (HNOMEMCHG:Ir.SmallStep.changes_mem i = false)
         (HINST:Ir.Config.cur_inst md st = Some i)
         (HOOM:Ir.SmallStep.inst_step md st Ir.SmallStep.sr_oom),
    False.
Proof.
  intros.
  inversion HOOM.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HINST in HNEXT.
    destruct i; des_ifs.
  - rewrite HINST in HCUR.
    inversion HCUR. rewrite HINST0 in H1.
    rewrite <- H1 in HNOMEMCHG. inversion HNOMEMCHG.
Qed.



(* Reordering between ptrtoint/ptrtoint:

   r1 = ptrtoint opptr1 ty1;
   r2 = ptrtoint opptr2 ty2
   ->
   r2 = ptrtoint opptr2 ty2;
   r1 = ptrtoint opptr1 ty1
*)
Lemma reorder_ptrtoint_ptrtoint:
  forall i1 i2 r1 r2 opptr1 opptr2 ty1 ty2
         (HINST1:i1 = Ir.Inst.iptrtoint r1 opptr1 ty1)
         (HINST2:i2 = Ir.Inst.iptrtoint r2 opptr2 ty2),
    inst_reordering_valid i1 i2.
Proof.
  intros.
  assert (HNOMEMCHG1:Ir.SmallStep.changes_mem i1 = false).
  { rewrite HINST1. reflexivity. }
  assert (HNOMEMCHG2:Ir.SmallStep.changes_mem i2 = false).
  { rewrite HINST2. reflexivity. }

  unfold inst_reordering_valid.
  intros.
  unfold has_data_dependency in HNODEP.
  rewrite HINST1, HINST2 in HNODEP.
  unfold Ir.Inst.regops in HNODEP.
  unfold Ir.regop in HNODEP.
  simpl in HNODEP.

  unfold inst_locates_at in *.
  destruct HLOCATE as [st_next [HLOCATE1 [HLOCATE_NEXT HLOCATE2]]].
  destruct HLOCATE' as [st_next' [HLOCATE1' [HLOCATE_NEXT' HLOCATE2']]].
  inv HSTEP.
  - inv HSUCC.
    + inv HSINGLE0; try congruence.
      unfold Ir.SmallStep.inst_det_step in HNEXT.
      des_ifs.
      * inv HSINGLE; try (rewrite cur_inst_update_reg_and_incrpc in *;
           apply incrpc'_incrpc in HLOCATE_NEXT;
           congruence).
        unfold Ir.SmallStep.inst_det_step in HNEXT.
        rewrite cur_inst_update_reg_and_incrpc in *.
        apply incrpc'_incrpc in HLOCATE_NEXT.
        rewrite HLOCATE_NEXT in HLOCATE2.
        rewrite HLOCATE2 in HNEXT.
        des_ifs.
        { (* i2 is ptrtoint <const(int)>. *)
          exists (nil, Ir.SmallStep.sr_goes_wrong).
          split.
          - eapply Ir.SmallStep.ns_goes_wrong.
            eapply Ir.SmallStep.ns_one.
            constructor. 
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'.
            unfold Ir.Config.get_val in *. inv Heq1. rewrite H0.
            reflexivity.
          - apply nseq_goes_wrong. reflexivity.
        }
        { (* i2 is ptrtoint <const(ptr)>. *)
          rewrite m_update_reg_and_incrpc.
          (* Needs to know that r1 != r2! from SSA property. *)
          eexists.
          split.
          - eapply Ir.SmallStep.ns_success.
            eapply Ir.SmallStep.ns_one.
            econstructor.
            unfold Ir.SmallStep.inst_det_step.
            rewrite HLOCATE1'. unfold Ir.Config.get_val in *. inv Heq1. rewrite H0.
            reflexivity.
            econstructor.
            unfold Ir.SmallStep.inst_det_step.
            rewrite cur_inst_update_reg_and_incrpc.
            apply incrpc'_incrpc in HLOCATE_NEXT'.
            rewrite HLOCATE_NEXT' in HLOCATE2'.
            rewrite HLOCATE2'.
            destruct opptr1. (* when i1's operand is constant *)
            + unfold Ir.Config.get_val in *. inv Heq0. rewrite H0.
              reflexivity.
            + rewrite get_val_independent. rewrite Heq0. reflexivity.
              admit. (* SSA property!! *)
          - rewrite m_update_reg_and_incrpc.
            apply nseq_success. reflexivity.
            apply config_eq_update_reg_and_incrpc.
      
inv HOOM.
    + inv HOOM0.
    + inv HSUCC.
      exfalso. eapply no_mem_change_no_oom.
      rewrite HNOMEMCHG1. reflexivity.
      eapply HLOCATE1. assumption.
  - inv HGW.
    + inv HGW0.
    + inv HSUCC.
      exists (Ir.e_none::nil, Ir.SmallStep.sr_goes_wrong).
      split.
      * eapply Ir.SmallStep.ns_success.
        eapply Ir.SmallStep.ns_success.


 Ir.Config.cur_inst md
           (Ir.SmallStep.update_reg_and_incrpc md st r1
              (Value.Ir.num (Ir.SmallStep.p2N p (Ir.Config.m st) n
        
        apply Ir.SmallStep.ns_success with (c' := c').
        constructor.
        
        
      inversion HSUCC.
      inversion HSINGLE.
      * inversion HSUCC.
        -- rewrite <- H12 in *. clear H12.
           unfold Ir.SmallStep.inst_det_step in HNEXT.
           rewrite HLOCATE1 in HNEXT.

Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).


End Reordering.

End Ir.
(* From:LoadStore.v *)



(* From:SmallStep.v *)

Ltac thats_it := eapply update_reg_and_incrpc_wf; eauto.
Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).
Ltac try_wf :=
  des_ifs; try (eapply update_reg_and_incrpc_wf; try eassumption;
                try reflexivity; try congruence; fail).


(* Lemma: inst_det_step preserves well-formedness of configuration. *)
Lemma inst_det_step_wf:
  forall c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNEXT:Some (sr_success e c') = inst_det_step c),
    Ir.Config.wf md c'.
Proof.
    intros.
    unfold inst_det_step in HNEXT. (* ibinop. *)
    rewrite <- HCUR in HNEXT.
    destruct i as [r retty bopc op1 op2 (* ibinop *)
                  |r retty ptrty opptr1 opptr2 (* ipsub *)
                  |r retty opptr opidx inb (* igep *)
                  |r retty opptr (* iload *)
                  |valty opval opptr (* istore *)
                  |(* imalloc *)
                  |opptr (* ifree *)
                  |r opval retty (* ibitcast *)
                  |r opptr retty (* iptrtoint *)
                  |r opint retty (* iinttoptr *)
                  |opval (* ievent *)
                  |r opty op1 op2 (* iicmp_eq *)
                  |r opty op1 op2 (* iicmp_ule *)
                  ] eqn:HINST; try (inversion HNEXT; fail).
    + destruct bopc; try_wf.
    + (* ipsub. *) unfold psub in HNEXT. try_wf.
    + (* igep. *) try_wf.
      eapply update_reg_and_incrpc_wf.
      eassumption. reflexivity.
      intros. unfold gep in HPTR. des_ifs.
      apply Ir.Memory.get_fresh_bid with (mb := t1). inv HWF. assumption.
      assumption.
      inv HWF. eapply wf_no_bogus_ptr. eassumption.
    + (* iload. *) try_wf.
      eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
      intros. inv HWF. eapply wf_no_bogus_ptr_mem.
      eassumption.
    + (* istore. *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty)).
      destruct HWF.
      split; simpl; try assumption. eapply Ir.store_val_wf. eassumption. reflexivity. congruence.
      intros. rewrite fresh_bid_store_val. eapply wf_no_bogus_ptr. eassumption.
      admit. (* store_val does not hamper wf_no_bogus_ptr_mem! *)
      reflexivity.
    + (* ifree *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c t0); try reflexivity.
      unfold free in Heq0.
      destruct HWF.
      des_ifs.
      * split. eapply Ir.Memory.free_wf. eassumption. rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_stack with (curcid := curcid) (funid := funid) (curregfile := curregfile).
        assumption. unfold Ir.Config.cid_to_f in *.
        unfold Ir.Config.update_m in HIN2. destruct c. simpl in *. assumption.
        assumption.
        admit. (* wf_no_bogus_ptr *)
        admit. (* wf_no_bogus_ptr_mem *)
      * split. eapply Ir.Memory.free_wf. eassumption. rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        intros. apply wf_stack with (curcid := curcid) (funid := funid) (curregfile := curregfile).
        assumption. unfold Ir.Config.cid_to_f in *.
        unfold Ir.Config.update_m in HIN2. destruct c. simpl in *. assumption.
        assumption.
        admit. (* wf_no_bogus_ptr *)
        admit. (* wf_no_bogus_ptr_mem *)
(*    + (* ibitcast. *) try_wf.
    + (* iptrtoint. *) try_wf.
    + (* iinttoptr *) try_wf.
    + (* ievent *)
      rename HNEXT into H2. simpl in H2.
      des_op c opval opv H2. des_inv opv H2.
      inversion H2. eapply incrpc_wf. eassumption. reflexivity.
    + (* iicmp_eq, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { destruct op1v.
        - des_op c op2 op2v HC'.
          destruct op2v; inversion HC'; thats_it. inv HC'. try_wf.
        - des_op c op2 op2v HC'.
          destruct op2v; try (inversion HC'; fail).
          inv HC'. try_wf.
          destruct (icmp_eq_ptr p p0 (Ir.Config.m c)) eqn:Heq_ptr; try (inversion HC'; fail);
             inversion HC'; thats_it.
          inversion HC'. thats_it.
          inv HC'. try_wf.
        - inversion HC'. thats_it. }
      { des_op c op2 op2v HC'.
        destruct op2v; try (inversion HC'; fail).
        inversion HC'. thats_it.
        inv HC'. try_wf. inv HC'. try_wf. inv HC'. try_wf.
      }
    + (* iicmp_ule, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { des_inv op1v HC';
          des_op c op2 op2v HC'; try (inv HC'; try_wf).
      }
      { des_ifs; try_wf. }
Qed.*)
Admitted.

(* Theorem: inst_step preserves well-formedness of configuration. *)
Theorem inst_step_wf:
  forall c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:inst_step c (sr_success e c')),
    Ir.Config.wf md c'.
(*Proof.
  intros.
  inversion HSTEP.
  - unfold inst_det_step in HNEXT.
    destruct (Ir.Config.cur_inst md c) as [i0|] eqn:Hcur.
    eapply inst_det_step_wf. eassumption.
    rewrite Hcur. reflexivity. unfold inst_det_step.
    rewrite Hcur. eassumption.
    inversion HNEXT.
  - (* imalloc with size 0 *)
    thats_it.
  - (* imalloc, succeed *)
    eapply update_reg_and_incrpc_wf with (c := Ir.Config.update_m c m').
    + inversion HWF.
      split; try (simpl; assumption).
      * simpl. eapply Ir.Memory.new_wf.
        eapply wf_m.
        eassumption.
        eassumption.
        eassumption.
    + reflexivity.
  - (* iicmp_eq, nondet *)
    eapply update_reg_and_incrpc_wf.
    eassumption.
    reflexivity.
  - (* icmp_ule, nondet *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
  - (* icmp_ule, nondet 2 *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
Qed.*)
Admitted.

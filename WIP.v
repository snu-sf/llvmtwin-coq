(* From:LoadStore.v *)



(* From:SmallStep.v *)




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

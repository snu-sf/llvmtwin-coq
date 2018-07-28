Require Import List.
Require Import Bool.
Require Import BinNat.
Require Import Omega.
Require Import sflib.

Require Import Common.
Require Import Memory.
Require Import Value.
Require Import Lang.
Require Import State.
Require Import LoadStore.
Require Import Behaviors.
Require Import SmallStep.
Require Import SmallStepAux.

Module Ir.

Module SmallStep.

Import SmallStep.
Import Ir.
Import Ir.SmallStep.
Import SmallStepAux.
Import Ir.
Import Ir.SmallStep.

(****************************************************
        Theorems about sstep of instruction.
 ****************************************************)

Theorem incrpc_wf:
  forall md c c'
         (HWF:Ir.Config.wf md c)
         (HC':c' = incrpc md c),
    Ir.Config.wf md c'.
Proof.
  (* High-level proof: incrpc changes stack frame only, and
     next_trivial_pc satisfies valid_pc. *) 
  intros.
  unfold incrpc in HC'.
  destruct (Ir.Config.cur_fdef_pc md c) eqn:HC.
  - destruct p as [fdef pc0].
    remember (Ir.IRFunction.next_trivial_pc pc0 fdef) as pc_next.
    destruct pc_next as [pc_next | ].
    unfold Ir.Config.update_pc in HC'.
    remember (Ir.Config.s c) as s'.
    destruct s' as [ | [cid [pc0' r0']] st] .
    + congruence.
    + (* show that pc0' = pc0 *)
      unfold Ir.Config.cur_fdef_pc in HC.
      rewrite <- Heqs' in HC.
      remember (Ir.Config.get_funid c cid) as ofunid.
      destruct ofunid as [funid | ]; try (inversion HC; fail).
      remember (Ir.IRModule.getf funid md) as ofdef'.
      destruct ofdef' as [fdef' | ]; try (inversion HC; fail).
      inversion HC.
      rewrite H0, H1 in *.
      clear H0 H1 HC.
      (* Now prove Ir.Config.wf c' *)
      rewrite HC'.
      inversion HWF.
      split.
      * assumption.
      * assumption.
      * assumption.
      * simpl.
        intros.
        rewrite <- Heqs' in wf_stack.
        simpl in wf_stack.
        destruct HIN.
        -- inversion H. rewrite H1, H2, H3 in *. clear H H1 H2 H3.
           apply Ir.IRFunction.next_trivial_pc_valid with (pc1 := pc0).
           apply wf_stack with (curcid0 := curcid) (funid := funid0) (curregfile0 := curregfile).
           left. reflexivity.
           eassumption. assumption.
           assert (HINCID:Some funid0 = Ir.Config.get_funid c curcid).
           { eapply Ir.Config.cid_to_f_In_get_funid. eassumption. assumption. }
           rewrite <- Heqofunid in HINCID.
           inversion HINCID.
           rewrite H0 in HF. rewrite <- HF in Heqofdef'.
           inversion Heqofdef'. rewrite <- H1. congruence.
         -- apply wf_stack with (curcid := curcid) (funid := funid0) (curregfile := curregfile).
            right. assumption. assumption. assumption.
      * simpl. intros.
        eapply wf_ptr. erewrite <- get_val_incrpc with (md := md).
        unfold incrpc. unfold Ir.Config.cur_fdef_pc. rewrite <- Heqs'.
        rewrite <- Heqofunid. rewrite <- Heqofdef'.
        rewrite <- Heqpc_next. unfold Ir.Config.update_pc.
        rewrite <- Heqs'. eassumption.
      * simpl. intros. eapply wf_ptr_mem.
        eassumption. eassumption. eassumption.
    + congruence.
  - congruence.
Qed.



Theorem update_rval_wf:
  forall md c c' r v
         (HWF:Ir.Config.wf md c)
         (HC':c' = Ir.Config.update_rval c r v)
         (HPTRWF:forall p, v = Ir.ptr p -> Ir.Config.ptr_wf p (Ir.Config.m c)),
    Ir.Config.wf md c'.
Proof.
  intros.
  inversion HWF.
  unfold Ir.Config.update_rval in HC'.
  rewrite HC'. clear HC'.
  destruct (Ir.Config.s c) as [ | [cid0 [pc0 reg0]] s'] eqn:Hs.
  { split; try assumption.
    intros. rewrite Hs in HIN. inversion HIN. }
  { split; try (simpl; assumption).
    simpl. intros.
    destruct HIN.
    - inversion H.
      destruct curregfile; inversion H3.
      rewrite H1, H2 in *. clear H1 H2.
      eapply wf_stack with (curcid0 := curcid). simpl. left. reflexivity.
      eassumption. assumption.
    - eapply wf_stack.
      simpl. right. eassumption. eassumption. assumption.
    - simpl. intros.
      unfold Ir.Config.get_val in HGETVAL.
      unfold Ir.Config.get_rval in HGETVAL.
      simpl in HGETVAL.
      destruct op eqn:Hop.
      + eapply wf_ptr with (op := op). unfold Ir.Config.get_val. 
        des_ifs.
      + destruct (Nat.eqb r r0) eqn:Hreg.
        { apply HPTRWF with (p := p).
          rewrite Nat.eqb_eq in Hreg. subst r0.
          rewrite Ir.Regfile.get_update in HGETVAL. congruence. }
        { rewrite Nat.eqb_neq in Hreg.
          rewrite Ir.Regfile.get_update2 in HGETVAL; try congruence.
          eapply wf_ptr with (op := Ir.opreg r0).
          unfold Ir.Config.get_val. unfold Ir.Config.get_rval.
          des_ifs. }
  }
Qed.

Theorem update_reg_and_incrpc_wf:
  forall md c c' v r
         (HWF:Ir.Config.wf md c)
         (HC':c' = update_reg_and_incrpc md c r v)
         (HPTRWF:forall p, v = Ir.ptr p -> Ir.Config.ptr_wf p (Ir.Config.m c)),
    Ir.Config.wf md c'.
Proof.
  intros.
  unfold update_reg_and_incrpc in HC'.
  assert (Ir.Config.wf md (Ir.Config.update_rval c r v)).
  { eapply update_rval_wf. eassumption. reflexivity.  eassumption. }
  rewrite HC'.
  eapply incrpc_wf.
  eapply H. reflexivity.
Qed.


Theorem t_step_wf:
  forall md c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:t_step md c = sr_success e c'),
    Ir.Config.wf md c'.
Proof.
  intros.
  inv HWF.
  unfold t_step in HSTEP.
  des_ifs.
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq3. rewrite Heq3 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq5. rewrite Heq5 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
  { unfold br in HSTEP.
    des_ifs.
    split; try (unfold Ir.Config.update_pc; des_ifs; done).
    { unfold Ir.Config.update_pc.
      simpl in wf_stack. simpl.
      intros.
      destruct (Ir.Config.s c) eqn:HS.
      { rewrite HS in HIN. inv HIN. }
      destruct p1. destruct p1. simpl in *.
      destruct HIN.
      { inv H.
        unfold Ir.Config.cur_fdef_pc in Heq0.
        rewrite HS in Heq0.
        unfold Ir.Config.get_funid in Heq0.
        des_ifs.
        apply list_find_key_In in HIN2.
        rewrite Heq0 in HIN2.
        assert (List.length (p::l) < 2).
        { eapply list_find_key_NoDup.
          eapply wf_cid_to_f.
          rewrite Heq0. reflexivity. }
        destruct l.
        { inv HIN2; try inv H0.
          simpl in Heq5. rewrite Heq5 in HF. inv HF.
          eapply Ir.IRFunction.get_begin_pc_bb_valid.
          eassumption.
        }
        { simpl in H. omega. }
      }
      { eapply wf_stack.
        { right. eassumption. }
        { eassumption. }
        { eassumption. }
      }
    }
    { simpl. intros.
      rewrite Ir.Config.m_update_pc. rewrite Ir.Config.get_val_update_pc in HGETVAL.
      eapply wf_ptr. eassumption. }
  }
Qed.

Ltac thats_it := eapply update_reg_and_incrpc_wf; eauto.
Ltac des_op c op op' HINV :=
  destruct (Ir.Config.get_val c op) as [op' | ]; try (inversion HINV; fail).
Ltac des_inv v HINV :=
  destruct (v); try (inversion HINV; fail).
Ltac try_wf :=
  des_ifs; try (eapply update_reg_and_incrpc_wf; try eassumption;
                try reflexivity; try congruence; fail).

Lemma OPAQUED_PTRSZ_PTRSZ:
  Ir.SmallStep.OPAQUED_PTRSZ = Ir.PTRSZ.
Proof.
  unfold Ir.SmallStep.OPAQUED_PTRSZ.
  unfold Ir.SmallStep.locked.
  des_ifs.
Qed.

Lemma PTRSZ_MEMSZ:
  Nat.shiftl 2 (Ir.PTRSZ - 1) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Lemma PTRSZ_MEMSZ2:
  Nat.double (Nat.shiftl 1 (Ir.PTRSZ - 1)) = Ir.MEMSZ.
Proof. reflexivity. Qed.

Lemma twos_compl_add_lt:
  forall a b,
    twos_compl_add a b Ir.PTRSZ < Ir.MEMSZ.
Proof.
  unfold twos_compl_add. unfold twos_compl.
  intros. rewrite PTRSZ_MEMSZ. apply Nat.mod_upper_bound.
  pose Ir.MEMSZ_pos. omega.
Qed.

Lemma gep_wf:
  forall p n t m inb p0
         (HGEP:gep p n t m inb = Ir.ptr p0)
         (HMWF:Ir.Memory.wf m)
         (HPWF:Ir.Config.ptr_wf p m),
    Ir.Config.ptr_wf p0 m.
Proof.
  intros.
  unfold gep in HGEP.
  inv HPWF.
  des_ifs.
  { exploit H. ss. intros HH. inv HH. inv H2.
    rewrite Heq in H3. inv H3.
    split.
    { intros. inv H2.
      split.
      rewrite OPAQUED_PTRSZ_PTRSZ.
      apply twos_compl_add_lt.
      eauto.
    }
    { intros. ss. }
  }
  { exploit H. ss. intros HH. inv HH. inv H2.
    split.
    { intros. inv H2. split.
      rewrite OPAQUED_PTRSZ_PTRSZ. apply twos_compl_add_lt.
      eauto. }
    { intros. ss. }
  }
  { exploit H0. ss. intros HH.
    split.
    { intros. ss. }
    { intros. inv H1. rewrite OPAQUED_PTRSZ_PTRSZ.
      apply twos_compl_add_lt. }
  }
  { exploit H0. ss. intros HH.
    split.
    { intros. ss. }
    { intros. inv H1. rewrite OPAQUED_PTRSZ_PTRSZ.
      apply twos_compl_add_lt. }
  }
  { exploit H0. ss. intros HH.
    split.
    { intros. ss. }
    { intros. inv H1. rewrite OPAQUED_PTRSZ_PTRSZ.
      apply twos_compl_add_lt. }
  }
Qed.

Lemma firstn_In {X:Type}:
  forall (l:list X) n x l'
         (HF:List.firstn n l = l')
         (HIN:List.In x l'),
    List.In x l.
Proof.
  intros.
  generalize dependent l.
  generalize dependent l'.
  induction n.
  { intros. simpl in HF. inv HF. inv HIN. }
  { simpl. intros.
    destruct l. inv HF. inv HIN.
    destruct l'; try congruence.
    inv HF. inv HIN. left. ss.
    right. eapply IHn. eassumption. ss.
  }
Qed.

Lemma skipn_In {X:Type}:
  forall (l:list X) n x l'
         (HF:List.skipn n l = l')
         (HIN:List.In x l'),
    List.In x l.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n.
  { intros. simpl in HF. congruence. }
  { simpl. intros.
    destruct l. congruence.
    eapply IHn in HF. right. ss. ss.
  }
Qed.

Lemma bytes_In_c:
  forall mb ofs len byt b
         (HBYTES:Ir.MemBlock.bytes mb ofs len = byt)
         (HIN:List.In b byt),
    List.In b (Ir.MemBlock.c mb).
Proof.
  intros.
  unfold Ir.MemBlock.bytes in HBYTES.
  rewrite <- HBYTES in HIN.
  eapply firstn_In in HIN; try ss.
  eapply skipn_In in HIN; try ss.
  ss.
Qed.

Lemma getpbits_ptr_in_byte:
  forall x p n
    (HPBITS:Ir.Byte.getpbits x = Some (p, n)),
    Ir.Config.ptr_in_byte p n x.
Proof.
  intros.
  unfold Ir.Byte.getpbits in HPBITS.
  unfold Ir.Config.ptr_in_byte.
  des_ifs.
  eauto.
Qed.

Lemma load_val_ptr_wf:
  forall md st p retty p0
         (HLOAD:Ir.load_val (Ir.Config.m st) p retty = Ir.ptr p0)
         (HWF:Ir.Config.wf md st)
         (HPWF:Ir.Config.ptr_wf p (Ir.Config.m st)),
    Ir.Config.ptr_wf p0 (Ir.Config.m st).
Proof.
  intros.
  unfold Ir.load_val in HLOAD.
  des_ifs.
  unfold Ir.Byte.getptr in Heq.
  unfold Ir.ty_bytesz in Heq.
  unfold Ir.ty_bitsz in Heq.
  unfold Ir.PTRSZ in Heq.
  simpl in Heq.
  des_ifs.
  unfold Ir.load_bytes in Heq1.
  des_ifs.
  dup Heq.
  apply Ir.get_deref_singleton in Heq4. inv Heq4; try congruence.
  inv H. inv H0. inv H. simpl in H1.
  assert (exists x, l = x::nil).
  { 
    destruct l; simpl in Heq0; try( inv Heq0; fail).
    rewrite Nat.eqb_eq in Heq0.
    destruct l. simpl in Heq0. eexists. reflexivity.
    simpl in Heq0. omega.
  }
  inv H. simpl in Heq0.
  simpl in Heq3. des_ifs.
  inv HWF.
  exploit wf_ptr_mem.
  { rewrite H1.  reflexivity. }
  { eapply bytes_In_c. eassumption.
    assert (In t0 [t0;x]). left. ss. eapply H. }
  { eapply getpbits_ptr_in_byte. eassumption. }
  intros. ss.
  { inv HWF. ss. }
  omega.
Qed.

Lemma store_val_ptr_wf:
  forall md p0 c p v valty
         (HWF:Ir.Config.wf md c)
         (HPWF:Ir.Config.ptr_wf p0 (Ir.Config.m c)),
  Ir.Config.ptr_wf p0 (Ir.store_val (Ir.Config.m c) p v valty).
Proof.
  intros.
  inv HPWF.
  destruct p0.
  { exploit H. ss. intros HH. inv HH. inv H2.
    split.
    { intros. inv H2. split. ss.
      unfold Ir.store_val. des_ifs; eauto.
      { unfold Ir.store_bytes.
        des_ifs; eauto.
        destruct (b =? l) eqn:HEQ.
        { rewrite Nat.eqb_eq in HEQ. subst b.
          erewrite Ir.Memory.get_set_id_short; try eassumption.
          eexists. ss. inv HWF. ss. }
        { rewrite Ir.Memory.get_set_diff_short. eexists. eassumption.
          inv HWF. ss. rewrite Nat.eqb_neq in HEQ. congruence. }
      }
      { unfold Ir.store_bytes.
        des_ifs; eauto.
        destruct (b =? l) eqn:HEQ.
        { rewrite Nat.eqb_eq in HEQ. subst b.
          erewrite Ir.Memory.get_set_id_short; try eassumption.
          eexists. ss. inv HWF. ss. }
        { rewrite Ir.Memory.get_set_diff_short. eexists. eassumption.
          inv HWF. ss. rewrite Nat.eqb_neq in HEQ. congruence. }
      }
    }
    { intros. congruence. }
  }
  { exploit H0. ss. intros HH.
    split.
    { intros. congruence. }
    { intros. inv H1. ss. }
  }
Qed.

Lemma N_to_bits_notbaddr:
  forall n b
         (HIN:List.In b (Ir.Bit.N_to_bits n)),
    forall p ofs, b <> Ir.Bit.baddr p ofs.
Proof.
  intros n b HIN.
  generalize dependent b.
  induction n.
  { intros. simpl in HIN. inv HIN. }
  { intros.
    simpl in HIN.
    generalize dependent b.
    induction p.
    { simpl. intros. destruct HIN. rewrite <- H. ss.
      apply IHp in H. ss. }
    { simpl. intros. destruct HIN. rewrite <- H. ss.
      apply IHp in H. ss. }
    { simpl. intros. inv HIN. ss. inv H. }
  }
Qed.

Lemma Forall_app {X:Type}:
  forall (l1 l2:list X) (f:X -> Prop)
         (HF:Forall f (l1++l2)),
    Forall f l1 /\ Forall f l2.
Proof.
  intros.
  induction l1.
  simpl in HF. split. ss. ss.
  simpl in HF. inv HF. split. constructor. ss.
  apply IHl1 in H2. inv H2. ss.
  apply IHl1 in H2. inv H2. ss.
Qed.

Lemma Forall_app2 {X:Type}:
  forall (l1 l2:list X) (f:X -> Prop)
         (HF1:Forall f l1)
         (HF2:Forall f l2),
    Forall f (l1 ++ l2).
Proof.
  intros.
  induction l1.
  simpl. ss.
  inv HF1. apply IHl1 in H2. simpl. constructor.
  ss. ss.
Qed.

Lemma Forall_repeat {X:Type}:
  forall x n (f:X -> Prop)
         (HF:f x),
    Forall f (List.repeat x n).
Proof.
  intros.
  induction n.
  simpl. ss.
  simpl. constructor. ss. ss.
Qed.

Lemma add_hzerobits_notbaddr:
  forall bits n
         (HFORALL:List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs) bits),
    List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs)
                (Ir.Bit.add_hzerobits bits n).
Proof.
  intros.
  unfold Ir.Bit.add_hzerobits.
  apply Forall_app2. ss.
  apply Forall_repeat. ss.
Qed.

Lemma from_bits_notbaddr:
  forall bits
         (HFORALL:List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs) bits),
    List.Forall (fun b =>
                   forall p ofs, b.(Ir.Byte.b0) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b1) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b2) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b3) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b4) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b5) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b6) <> Ir.Bit.baddr p ofs /\
                                 b.(Ir.Byte.b7) <> Ir.Bit.baddr p ofs) (Ir.Byte.from_bits bits).
Proof.
  intros.
  remember (Ir.Byte.from_bits bits) as byt.
  generalize dependent bits.
  induction byt.
  { simpl. intros. constructor. }
  { intros.
    destruct bits. simpl in Heqbyt.  inv Heqbyt.
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7.
      repeat (split; try congruence).
      constructor. }
    destruct bits.
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7 . inv H8.
      repeat (split; try congruence).
      constructor. }
    { simpl in Heqbyt. inv Heqbyt. constructor. simpl.
      inv HFORALL. inv H2. inv H4. inv H5. inv H6. inv H7 . inv H8. inv H9.
      repeat (split; try congruence).
    remember (t::t0::t1::t2::t3::t4::t5::t6::nil) as l.
    assert (t::t0::t1::t2::t3::t4::t5::t6::bits = l ++ bits).
    { rewrite Heql. reflexivity. }
    rewrite H in *.
    apply Forall_app in HFORALL. inv HFORALL.
    exploit IHbyt. eassumption. ss. eauto.
    }
  }
Qed.


Lemma In_ofint_not_ptr_in_byte:
  forall n1 len b p0 ofs
         (HIN:In b (Ir.Byte.ofint n1 len)),
    ~ Ir.Config.ptr_in_byte p0 ofs b.
Proof.
  intros.
  unfold Ir.Byte.ofint in HIN.
  remember (Ir.Bit.add_hzerobits (Ir.Bit.N_to_bits n1) (len - length (Ir.Bit.N_to_bits n1)))
           as bits.
  assert (List.Forall (fun b => forall p ofs, b <> Ir.Bit.baddr p ofs) bits).
  { rewrite Heqbits.
    eapply add_hzerobits_notbaddr.
    rewrite Forall_forall.
    intros.
    eapply N_to_bits_notbaddr. eassumption.
  }
  eapply from_bits_notbaddr in H.
  rewrite Forall_forall in H.
  apply H with (p := p0) (ofs := ofs) in HIN.
  intros HH.
  unfold Ir.Config.ptr_in_byte in HH.
  intuition.
Qed.

Lemma ptr_wf_set:
  forall p1 c b mb'
    (HMWF:Ir.Memory.wf (Ir.Config.m c))
    (HPTRWF:Ir.Config.ptr_wf p1 (Ir.Config.m c)),
    Ir.Config.ptr_wf p1 (Ir.Memory.set (Ir.Config.m c) b mb').
Proof.
  intros.
  destruct p1.
  { inv HPTRWF. exploit H. ss. intros HH. inv HH.
    inv H2.
    split.
    { intros. inv H2. split. ss.
      destruct (l =? b) eqn:HEQ.
      { rewrite Nat.eqb_eq in HEQ. subst l.
        erewrite Ir.Memory.get_set_id_short. eexists. ss.
        ss. eassumption. }
      { erewrite Ir.Memory.get_set_diff_short. eexists. eassumption.
        ss. rewrite Nat.eqb_neq in HEQ. congruence.
      }
    }
    { intros. congruence. }
  }
  { inv HPTRWF. exploit H0. ss. intros HH.
    split.
    { intros. congruence. }
    { intros. inv H1. eauto. }
  }
Qed.

Lemma store_val_ptr_mem_wf:
  forall md c opptr mb p v valty bid byt p0 ofs mb0
         (HWF:Ir.Config.wf md c)
         (HOPVAL:Ir.Config.get_val c opptr = Some v)
         (HGET0:Some mb0 = Ir.Memory.get (Ir.Config.m c) bid)
         (HGET:Some mb = Ir.Memory.get (Ir.store_val (Ir.Config.m c) p v valty) bid)
         (HIN:In byt (Ir.MemBlock.c mb))
         (HPTR:Ir.Config.ptr_in_byte p0 ofs byt),
    Ir.Config.ptr_wf p0 (Ir.store_val (Ir.Config.m c) p v valty).
Proof.
  intros.
  unfold Ir.store_val in *.
  des_ifs; try (inv HWF; eapply wf_ptr_mem; eassumption).
  { unfold Ir.store_bytes in *.
    des_ifs;
      try (inv HWF; eapply wf_ptr_mem; eassumption).
    eapply Ir.get_deref_singleton in Heq0.
    destruct Heq0; try congruence.
    destruct H. destruct H. inv H. simpl in H0.
    destruct (b =? bid) eqn:HBID.
    { rewrite Nat.eqb_eq in HBID. subst bid.
      erewrite Ir.Memory.get_set_id in HGET.
      3: rewrite <- HGET0; reflexivity.
      3: reflexivity.
      inv HGET.
      unfold Ir.MemBlock.set_bytes in HIN.
      simpl in HIN.
      apply List.in_app_or in HIN.
      destruct HIN.
      { (* unchanged part *)
        inv HWF.
        eapply ptr_wf_set. ss. eapply wf_ptr_mem.
        rewrite H0. ss.
        eapply firstn_In. ss. eassumption. eassumption.
      }
      apply List.in_app_or in H.
      destruct H.
      { (* changed part! but it's integer. *)
        eapply In_ofint_not_ptr_in_byte in H.
        eapply H in HPTR. inv HPTR.
      }
      { (* unchanged part. *)
        inv HWF.
        eapply ptr_wf_set. ss. eapply wf_ptr_mem.
        rewrite H0. ss.
        eapply skipn_In. ss. eassumption. eassumption.
      }
      { inv HWF. ss. }
    }
    { (* b <> bid *)
      rewrite Ir.Memory.get_set_diff_short in HGET.
      inv HWF.
      eapply ptr_wf_set. ss. eapply wf_ptr_mem.
      rewrite HGET. ss. eassumption. eassumption.
      inv HWF. ss.
      rewrite Nat.eqb_neq in HBID. congruence.
    }
    inv HWF. ss.
    rewrite Nat.eqb_eq in Heq. rewrite <- Heq.
    apply Ir.ty_bytesz_pos.
  }
  { (* stored value is ptr. *)
    unfold Ir.store_bytes in *.
    des_ifs; try (inv HWF; eauto; fail).
    eapply Ir.get_deref_singleton in Heq0.
    destruct Heq0; try congruence.
    inv H. inv H0. inv H. simpl in H1.
    destruct (b =? bid) eqn:HBID.
    { rewrite Nat.eqb_eq in HBID. subst bid.
      erewrite Ir.Memory.get_set_id in HGET.
      3: eapply H1. 3: reflexivity.
      inv HGET.
      unfold Ir.MemBlock.set_bytes in *.
      simpl in *.
      eapply List.in_app_or in HIN.
      destruct HIN.
      { (* unchangd part *)
        inv HWF.
        eapply ptr_wf_set. ss. eapply wf_ptr_mem.
        rewrite H1. ss. eapply firstn_In. ss. eassumption. eassumption.
      }
      simpl in H.
      destruct H.
      { (* changed part 1 *)
        (* should use ptr_wf *)
        rewrite <- H in HPTR.
        unfold Ir.Config.ptr_in_byte in HPTR. simpl in HPTR.
        inv HWF. dup HOPVAL.
        apply wf_ptr in HOPVAL.
        assert (HP0P1:p0 = p1).
        { destruct HPTR. congruence.
          repeat (destruct H; try congruence). }
        subst p0.
        eapply ptr_wf_set. ss. eapply wf_ptr. eassumption.
      }
      destruct H. (* one more time *)
      { 
        (* should use ptr_wf *)
        rewrite <- H in HPTR.
        unfold Ir.Config.ptr_in_byte in HPTR. simpl in HPTR.
        inv HWF. dup HOPVAL.
        apply wf_ptr in HOPVAL.
        assert (HP0P1:p0 = p1).
        { destruct HPTR. congruence.
          repeat (destruct H; try congruence). }
        subst p0.
        eapply ptr_wf_set. ss. eapply wf_ptr. eassumption.
      }
      (* unchanged part *)
      inv HWF.
      eapply ptr_wf_set. ss. eapply wf_ptr_mem. rewrite H1. ss.
      eapply skipn_In. ss. eassumption. eassumption.
      inv HWF. ss.
    }
    { (* b <> bid *)
      rewrite Ir.Memory.get_set_diff_short in HGET.
      inv HWF.
      eapply ptr_wf_set. ss. eapply wf_ptr_mem.
      rewrite HGET. ss. eassumption. eassumption.
      inv HWF. ss.
      rewrite Nat.eqb_neq in HBID. congruence.
    }
    inv HWF. ss.
    rewrite Nat.eqb_eq in Heq. rewrite <- Heq.
    apply Ir.ty_bytesz_pos.
  }
Qed.

Lemma list_find_key_set_none2:
  forall (X : Type) (m : list (nat * X)) (k k' : nat) (v : X),
  list_find_key m k = [] -> list_find_key (list_set m k' v) k = [].
Proof.
  intros.
  induction m.
  { reflexivity. }
  { simpl.
    simpl in H. des_ifs. simpl in Heq. rewrite Nat.eqb_eq in *. subst. rewrite Nat.eqb_refl in Heq1. ss.
    apply IHm. ss.
    eauto.
  }
Qed.

Lemma get_set_exists:
  forall m b bid mb mb'
         (HGET:Some mb = Ir.Memory.get (Ir.Memory.set m b mb') bid),
    exists mb'', Some mb'' = Ir.Memory.get m bid.
Proof.
  intros.
  unfold Ir.Memory.get in *.
  unfold Ir.Memory.set in *.
  simpl in *.
  des_ifs.
  eapply list_find_key_set_none2 with (k' := b) (v := mb') in Heq.
  rewrite Heq in Heq0. ss.
  eexists. ss.
Qed.

Lemma s_update_m:
  forall c t,
    Ir.Config.s (Ir.Config.update_m c t) = Ir.Config.s c.
Proof.
  reflexivity.
Qed.

Lemma free_ptr_wf:
  forall c b t p
    (HMWF:Ir.Memory.wf (Ir.Config.m c))
    (HFREE: Ir.Memory.free (Ir.Config.m c) b = Some t)
    (HWF:Ir.Config.ptr_wf p (Ir.Config.m c)),
    Ir.Config.ptr_wf p t.
Proof.
  intros.
  inv HWF.
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct p.
  { exploit H. ss. intros HH. inv HH. inv H2.
    split.
    { intros. inv H2. split. ss.
      destruct (b =? l) eqn:HEQ.
      { rewrite Nat.eqb_eq in HEQ.  subst b.
        erewrite Ir.Memory.get_set_id_short. eexists. ss.
        eapply Ir.Memory.incr_time_wf. eassumption.
        ss.
        rewrite Ir.Memory.get_incr_time_id. eassumption.
      }
      { rewrite Ir.Memory.get_set_diff_short.
        rewrite Ir.Memory.get_incr_time_id. eexists. eassumption.
        eapply Ir.Memory.incr_time_wf. eassumption. ss.
        rewrite Nat.eqb_neq in HEQ. congruence.
      }
    }
    { intros. congruence. }
  }
  { exploit H0. ss. intros HH.
    split.
    { intros. congruence. }
    { intros. inv H1. ss. }
  }
Qed.

Lemma get_free_c:
  forall m m' b bid mb mb'
         (HWF:Ir.Memory.wf m)
         (HFREE:Ir.Memory.free m b = Some m')
         (HGET:Some mb = Ir.Memory.get m bid)
         (HGET':Some mb' = Ir.Memory.get m' bid),
    Ir.MemBlock.c mb = Ir.MemBlock.c mb'.
Proof.
  intros.
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (b =? bid) eqn:HEQ.
  { rewrite Nat.eqb_eq in HEQ.
    subst b.
    erewrite Ir.Memory.get_set_id_short in HGET'. inv HGET'.
    unfold Ir.MemBlock.set_lifetime_end in Heq2.
    des_ifs. simpl. congruence.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Ir.Memory.get_incr_time_id. rewrite HGET. ss.
  }
  { rewrite Ir.Memory.get_set_diff_short in HGET'.
    rewrite Ir.Memory.get_incr_time_id in HGET'. congruence.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Nat.eqb_neq in HEQ. congruence.
  }
Qed.

Lemma get_free_some_inv:
  forall (m m' : Ir.Memory.t) (l l0 : Ir.blockid) (blk : Ir.MemBlock.t)
         (HWF:Ir.Memory.wf m)
         (HFREE:Some m' = Ir.Memory.free m l0)
         (HGET:Ir.Memory.get m' l = Some blk),
  exists blk' : Ir.MemBlock.t, Ir.Memory.get m l = Some blk'.
Proof.
  intros.
  unfold Ir.Memory.free in HFREE.
  des_ifs.
  destruct (l0 =? l) eqn:HEQ.
  { rewrite Nat.eqb_eq in HEQ.
    subst. eexists. eassumption. }
  { erewrite Ir.Memory.get_set_diff_short in HGET.
    rewrite Ir.Memory.get_incr_time_id in HGET.
    eexists. eapply HGET.
    eapply Ir.Memory.incr_time_wf. eassumption.
    ss. rewrite Nat.eqb_neq in HEQ. congruence.
  }
Qed.

Lemma twos_compl_lt:
  forall a,
    twos_compl a Ir.PTRSZ < Ir.MEMSZ.
Proof.
  unfold twos_compl.
  intros. rewrite PTRSZ_MEMSZ. apply Nat.mod_upper_bound.
  pose Ir.MEMSZ_pos. omega.
Qed.


(* Lemma: inst_det_step preserves well-formedness of configuration. *)
Lemma inst_det_step_wf:
  forall md c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNEXT:Some (sr_success e c') = inst_det_step md c),
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
      eapply update_reg_and_incrpc_wf; try reflexivity.
      eassumption.
      intros. eapply gep_wf; try eassumption.
      inv HWF. assumption. inv HWF. eapply wf_ptr; eassumption.
    + (* iload. *) try_wf.
      eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
      intros. dup HWF. inv HWF.
      eapply load_val_ptr_wf. eassumption. eassumption.
      eapply wf_ptr. eassumption.
    + (* istore. *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c (Ir.store_val (Ir.Config.m c) p v valty)).
      dup HWF. destruct HWF.
      split; simpl; try assumption. eapply Ir.store_val_wf. eassumption.
      eapply Ir.ty_bytesz_pos. congruence.
      * intros. rewrite Ir.Config.get_val_update_m in HGETVAL.
        eapply store_val_ptr_wf. eassumption.
        eapply wf_ptr in HGETVAL. ss.
      * (* wf_ptr_mem *)
        intros.
        assert (exists mb', Some mb' = Ir.Memory.get (Ir.Config.m c) bid).
        { unfold Ir.store_val in HBLK. unfold Ir.store_bytes in HBLK.
          des_ifs; try (eexists; rewrite HBLK; reflexivity).
          eapply get_set_exists. eassumption.
          eapply get_set_exists. eassumption.
        }
        inv H.
        eapply store_val_ptr_mem_wf; try eassumption.
      * ss.
    + (* ifree *) try_wf; try (eapply incrpc_wf; try eassumption; try reflexivity; fail).
      apply incrpc_wf with (c := Ir.Config.update_m c t); try reflexivity.
      unfold free in Heq0.
      destruct HWF.
      des_ifs.
      * split.
        -- eapply Ir.Memory.free_wf. eassumption.
           rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        -- unfold Ir.Config.cid_to_f in *. des_ifs.
        -- intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        -- intros. rewrite s_update_m in HIN. eauto.
        -- intros.
           rewrite Ir.Config.get_val_update_m in HGETVAL.
           rewrite Ir.Config.m_update_m.
           apply wf_ptr in HGETVAL.
           eapply free_ptr_wf; eassumption.
        -- intros. rewrite Ir.Config.m_update_m in *.
           dup HBLK. symmetry in HBLK.
           eapply get_free_some_inv in HBLK; try eauto.
           inv HBLK.
           erewrite <- get_free_c in HBYTE.
           3: eauto. 4: eauto. 3: eauto. 2: eauto.
           eapply free_ptr_wf. eassumption. eauto.
           eapply wf_ptr_mem. rewrite H. eauto. eauto. eauto.
      * split.
        -- eapply Ir.Memory.free_wf. eassumption.
           rewrite Heq0. unfold Ir.Config.update_m. reflexivity.
        -- unfold Ir.Config.cid_to_f in *. des_ifs.
        -- intros. apply wf_cid_to_f2. unfold Ir.Config.cid_to_f in *. des_ifs.
        -- intros.
           apply wf_stack with (curcid := curcid) (funid := funid) (curregfile := curregfile).
           assumption. unfold Ir.Config.cid_to_f in *.
           unfold Ir.Config.update_m in HIN2. destruct c. simpl in *. assumption.
           assumption.
        -- intros.
           rewrite Ir.Config.get_val_update_m in HGETVAL.
           rewrite Ir.Config.m_update_m.
           apply wf_ptr in HGETVAL.
           eapply free_ptr_wf; eassumption.
        -- intros. rewrite Ir.Config.m_update_m in *.
           dup HBLK. symmetry in HBLK.
           eapply get_free_some_inv in HBLK; try eauto.
           inv HBLK.
           eapply free_ptr_wf. eassumption. eassumption.
           eapply wf_ptr_mem.
           3: eapply HBIT.
           rewrite H. reflexivity.
           erewrite <- get_free_c in HBYTE. 3:eauto. 4:eauto. 3:eauto. 2:eauto.
           eauto.
    + (* ibitcast. *) try_wf.
      eapply update_reg_and_incrpc_wf. eassumption.
      reflexivity.
      intros. inv H.
      inv HWF. eapply wf_ptr. eassumption.
    + (* iptrtoint. *) try_wf.
    + (* iinttoptr *) try_wf.
      eapply update_reg_and_incrpc_wf; try eassumption.
      reflexivity.
      intros. inv H.
      split. intros. congruence.
      intros. inv H.
      rewrite OPAQUED_PTRSZ_PTRSZ. 
      eapply twos_compl_lt.
    + (* ievent *)
      rename HNEXT into H2. simpl in H2.
      des_op c opval opv H2. des_inv opv H2.
      inversion H2. eapply incrpc_wf. eassumption. reflexivity.
    + (* iicmp_eq, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { des_ifs;
        try (eapply update_reg_and_incrpc_wf;
             [ eassumption | ss | intros H1 H2; unfold to_num in H2; congruence ]).
      }
      { des_ifs;
        try (eapply update_reg_and_incrpc_wf;
             [ eassumption | ss | intros H1 H2; unfold to_num in H2; congruence ]).
      }
    + (* iicmp_ule, det *)
      rename HNEXT into HC'. simpl in HC'.
      des_op c op1 op1v HC'.
      { des_inv op1v HC';
          des_op c op2 op2v HC'; try (inv HC'; try_wf).
        try (eapply update_reg_and_incrpc_wf;
             [ eassumption | ss | intros H1 H2; unfold to_num in H2; congruence ]).
        try (eapply update_reg_and_incrpc_wf;
             [ eassumption | ss | intros H1 H2; unfold to_num in H2; congruence ]).
      }
      { des_ifs; try_wf. }
Qed.

(* Lemma: inst_step preserves well-formedness of configuration. *)
Lemma inst_step_wf:
  forall md c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:inst_step md c (sr_success e c')),
    Ir.Config.wf md c'.
Proof.
  intros.
  inversion HSTEP.
  - unfold inst_det_step in HNEXT.
    destruct (Ir.Config.cur_inst md c) as [i0|] eqn:Hcur.
    eapply inst_det_step_wf. eassumption.
    rewrite Hcur. reflexivity. unfold inst_det_step.
    rewrite Hcur. eassumption.
    inversion HNEXT.
  - (* imalloc returning null *)
    thats_it. unfold Ir.NULL.
    intros. inv H0.
    split. intros. congruence.
    intros. inv H. apply Ir.MEMSZ_pos.
  - (* imalloc, succeed *)
    eapply update_reg_and_incrpc_wf with (c := Ir.Config.update_m c m').
    + inversion HWF.
      split; try (simpl; assumption).
      * simpl. eapply Ir.Memory.new_wf.
        eapply wf_m.
        eassumption.
        eassumption.
        eassumption.
      * intros.
        rewrite Ir.Config.get_val_update_m in HGETVAL.
        admit.
      * admit.
    + reflexivity.
    + admit.
  - (* iicmp_eq, nondet *)
    eapply update_reg_and_incrpc_wf.
    eassumption.
    reflexivity.
    intros. congruence.
  - (* icmp_ule, nondet *)
    eapply update_reg_and_incrpc_wf. eassumption. reflexivity.
    intros. congruence.
Admitted.


Lemma phi_step_wf:
  forall md c c' bef_bbid
         (HWF:Ir.Config.wf md c)
         (HSTEP:phi_step md bef_bbid c = Some c'),
    Ir.Config.wf md c'.
Proof.
  intros.
  unfold phi_step in HSTEP.
  des_ifs.
  eapply update_reg_and_incrpc_wf. eassumption.
  ss.
  intros.
  inv HWF.
  eapply wf_ptr. eassumption.
Qed.

Lemma phi_bigstep_wf:
  forall md c c' bef_bbid
         (HWF:Ir.Config.wf md c)
         (HSTEP:phi_bigstep md bef_bbid c c'),
    Ir.Config.wf md c'.
Proof.
  intros.
  induction HSTEP.
  { eapply phi_step_wf; eassumption. }
  { apply IHHSTEP in HWF.
    eapply phi_step_wf. eassumption. eassumption.
  }
Qed.


(* Theorem: small step preserves well-formedness of configuration. *)
Theorem sstep_wf:
  forall md c c' e
         (HWF:Ir.Config.wf md c)
         (HSTEP:sstep md c (sr_success e c')),
    Ir.Config.wf md c'.
Proof.
  intros.
  inv HSTEP.
  { eapply inst_step_wf. eassumption. eassumption. }
  { assert (Ir.Config.wf md st').
    { eapply t_step_wf. eassumption. eassumption. }
    eapply phi_bigstep_wf; eassumption.
  }
Qed.


(****************************************************
   Theorems regarding categorization of instruction.
 ****************************************************)

Lemma no_mem_change_after_incrpc:
  forall md c,
    Ir.Config.m c = Ir.Config.m (incrpc md c).
Proof.
  intros.
  unfold incrpc.
  destruct (Ir.Config.cur_fdef_pc md c).
  destruct p.
  { des_ifs. unfold Ir.Config.update_pc.
    des_ifs. }
  reflexivity.
Qed.

Lemma no_mem_change_after_update:
  forall md c r v,
    Ir.Config.m c = Ir.Config.m (update_reg_and_incrpc md c r v).
Proof.
  intros.
  unfold update_reg_and_incrpc.
  rewrite <- no_mem_change_after_incrpc.
  unfold Ir.Config.update_rval.
  des_ifs.
Qed.

(* Lemma: inst_det_step preserves well-formedness of configuration. *)
Ltac thats_it2 := apply no_mem_change_after_update.

Lemma changes_mem_spec_det:
  forall md c c' i e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HNEXT:Some (sr_success e c') = inst_det_step md c),
    c.(Ir.Config.m) = c'.(Ir.Config.m).
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
                  ] eqn:HINST; try (inversion HNEXT; fail);
      try (inversion HNOMEMCHG; fail);
      try (des_ifs; thats_it2; fail).
    + (* ievent *)
      rename HNEXT into H2. simpl in H2.
      des_op c opval opv H2. des_inv opv H2.
      inversion H2. eapply no_mem_change_after_incrpc.
Qed.

(* Theorem: if changes_mem returns false, memory isn't
   changed after inst_step.
   This includes ptrtoint/inttoptr/psub/gep/icmp. *)
Theorem changes_mem_spec:
  forall md c i c' e
         (HWF:Ir.Config.wf md c)
         (HCUR:Some i = Ir.Config.cur_inst md c)
         (HNOMEMCHG:changes_mem i = false)
         (HSTEP:inst_step md c (sr_success e c')),
    c.(Ir.Config.m) = c'.(Ir.Config.m).
Proof.
  intros.
  inversion HSTEP.
  - eapply changes_mem_spec_det. eassumption.
    eassumption. assumption. eassumption.
  - (* malloc, NULL *)
    apply no_mem_change_after_update.
  - (* malloc *)
    rewrite <- HCUR in HCUR0. inversion HCUR0. rewrite H3 in HINST.
    rewrite HINST in HNOMEMCHG. inversion HNOMEMCHG.
  - (* iicmp_eq, nondet *) apply no_mem_change_after_update.
  - (* icmp_ule, nondet *) apply no_mem_change_after_update.
Qed.


End SmallStep.

End Ir.
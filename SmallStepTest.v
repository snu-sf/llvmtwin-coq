Require Import BinNat.
Require Import Bool.
Require Import List.
Require Import sflib.
Require Import Omega.
Require Import Lia.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Memory.
Require Import State.
Require Import LoadStore.
Require Import SmallStep.
Require Import SmallStepAux.
Require Import Behaviors.


Module Ir.

Module SmallStepTest.


Module GetElementPtr.

(****************************************************
            gep poison, idx is always poison.
 ****************************************************)

Theorem gep_poison1:
  forall st md r ptrty op1 opidx inb sr
         (HOP1:Ir.Config.get_val st op1 = Some Ir.poison)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r ptrty op1 opidx inb))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
Qed.

(****************************************************
            gep ptr, poison is always poison.
 ****************************************************)

Theorem gep_poison2:
  forall st md r ptrty op1 opidx inb sr
         (HOP1:Ir.Config.get_val st opidx = Some Ir.poison)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r ptrty op1 opidx inb))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
Qed.

(****************************************************
            gep log(l, 10), 5 is log(l, 15).
 ****************************************************)

Theorem gep_logical1:
  forall st md r ptrty op1 opidx sr l
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l 10)))
         (HOP2:Ir.Config.get_val st opidx = Some (Ir.num 5))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r (Ir.ptrty ptrty) op1 opidx false))
         (HSZ:Ir.ty_bytesz ptrty = 1)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := log (l, 15 * |ptrty|) *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.ptr (Ir.plog l 15))).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
  unfold Ir.SmallStep.gep. rewrite HSZ. simpl.
  assert (Ir.SmallStep.twos_compl_add 10 5 Ir.PTRSZ = 15).
  { unfold Ir.SmallStep.twos_compl_add.
    simpl. unfold Ir.SmallStep.twos_compl. rewrite Ir.PTRSZ_def.
    reflexivity. }
  rewrite H. ss.
Qed.

(****************************************************
            gep phy(10), 5 is phy(15)
 ****************************************************)

Theorem gep_physical1:
  forall st md r ptrty op1 opidx sr I cid
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.pphy 10 I cid)))
         (HOP2:Ir.Config.get_val st opidx = Some (Ir.num 5))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r (Ir.ptrty ptrty) op1 opidx false))
         (HSZ:Ir.ty_bytesz ptrty = 1)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := phy (l, 15 * |ptrty|) *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.ptr (Ir.pphy 15 I cid))).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
  unfold Ir.SmallStep.gep. rewrite HSZ. simpl.
  assert (Ir.SmallStep.twos_compl_add 10 5 Ir.PTRSZ = 15).
  { unfold Ir.SmallStep.twos_compl_add.
    simpl. unfold Ir.SmallStep.twos_compl. rewrite Ir.PTRSZ_def.
    reflexivity. }
  rewrite H. ss.
Qed.

(****************************************************
         gep inbounds log(l, 10), 5 is poison
             if l's size is less than 10.
 ****************************************************)

Theorem gep_inb_logical1:
  forall st md r ptrty op1 opidx sr l mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l 10)))
         (HOP2:Ir.Config.get_val st opidx = Some (Ir.num 5))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r (Ir.ptrty ptrty) op1 opidx true))
         (HSZ:Ir.ty_bytesz ptrty = 1)
         (HMB:Ir.Memory.get (Ir.Config.m st) l = Some mb)
         (HN: Ir.MemBlock.n mb < 10 * Ir.ty_bytesz ptrty)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
  unfold Ir.SmallStep.gep. rewrite HMB. rewrite HSZ in *. simpl.
  assert (Ir.SmallStep.twos_compl_add 10 5 Ir.PTRSZ = 15).
  { unfold Ir.SmallStep.twos_compl_add.
    simpl. unfold Ir.SmallStep.twos_compl. rewrite Ir.PTRSZ_def.
    reflexivity. }
  rewrite H. unfold Ir.MemBlock.inbounds.
  rewrite Nat.lt_nge in HN.
  rewrite <- Nat.leb_nle in HN.
  replace (10 * 1) with 10 in HN. rewrite HN. ss. ss.
Qed.

(****************************************************
         gep inbounds pphy(l, i), j is poison
     if j*Ir.ty_bytesz is positive &
        i+(j*Ir.ty_bytesz) is not smaller than MEMSZ.
 ****************************************************)

Theorem gep_inb_physical1:
  forall st md r ptrty op1 opidx sr i I cid j
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.pphy i I cid)))
         (HOP2:Ir.Config.get_val st opidx = Some (Ir.num j))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r (Ir.ptrty ptrty) op1 opidx true))
         (HN: Ir.MEMSZ <= i + j * Ir.ty_bytesz ptrty)
         (HPOS: j * Ir.ty_bytesz ptrty < Nat.shiftl 1 (Ir.PTRSZ - 1))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
  unfold Ir.SmallStep.gep.
  rewrite <- Nat.ltb_lt in HPOS. rewrite HPOS.
  rewrite Nat.le_ngt in HN.
  rewrite <- Nat.ltb_nlt in HN.
  rewrite HN. ss.
Qed.

(****************************************************
         gep inbounds pphy(l, i), j is poison
     if j*Ir.ty_bytesz is negative &
   i+(j*Ir.ty_bytesz) is smaller than Ir.MEMSZ
  (which means that, i-|j*Ir.ty_bytesz| is less than
   0)
 ****************************************************)

Theorem gep_inb_physical2:
  forall st md r ptrty op1 opidx sr i I cid j
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.pphy i I cid)))
         (HOP2:Ir.Config.get_val st opidx = Some (Ir.num j))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.igep r (Ir.ptrty ptrty) op1 opidx true))
         (HN: i + j * Ir.ty_bytesz ptrty < Ir.MEMSZ)
         (HNEG: Nat.shiftl 1 (Ir.PTRSZ - 1) <= j * Ir.ty_bytesz ptrty)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT. rewrite HCUR in HNEXT.
  inv HNEXT. des_ifs.
  unfold Ir.SmallStep.gep.
  rewrite Nat.le_ngt in HNEG.
  rewrite <- Nat.ltb_nlt in HNEG. rewrite HNEG.
  rewrite Nat.lt_nge in HN.
  rewrite <- Nat.leb_nle in HN.
  rewrite HN. ss.
Qed.

End GetElementPtr.


Module IcmpEq.

(****************************************************
            icmp eq 1, 2 is always false.
 ****************************************************)

Theorem icmp_eq_int_false:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 1))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 2))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOP1, HOP2 in HNEXT.
  inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp eq 15, 15 is always true.
 ****************************************************)

Theorem icmp_eq_int_true:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 15))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp eq poison, _ is poison.
 ****************************************************)

Theorem icmp_eq_poison:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
     icmp eq ptr1, ptr2 is equivalent to o1 == o2.
 ****************************************************)

Theorem icmp_eq_ptr_sameblock:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb) 
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 == o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r
                                               (Ir.SmallStep.to_num (Nat.eqb o1 o2))).
Proof.
  intros.
  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite PeanoNat.Nat.eqb_refl in HNEXT.
    inv HNEXT.
    reflexivity.
  - (* icmp cannot be nondeteministic. *)
    rewrite HCUR in HCUR0.
    inv HCUR0.
    rewrite HOP1 in HOP0. inv HOP0.
    rewrite HOP2 in HOP3. inv HOP3.
    unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond in HNONDET.
    rewrite HBLK in HNONDET.
    rewrite PeanoNat.Nat.eqb_refl in HNONDET.
    inv HNONDET.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 and o2 are smaller than block sizes
          & two blocks are still alive,
     icmp eq ptr1, ptr2 is false.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_false1:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 < Ir.MemBlock.n mb1) (* offset is smaller than block size *)
         (HOFS2:o2 < Ir.MemBlock.n mb2)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, None)) (* the blocks are alive *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, None))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)).
Proof.
  intros.
  assert (HNEQ1: o1 <> Ir.MemBlock.n mb1). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ1.
  assert (HNEQ2: o2 <> Ir.MemBlock.n mb2). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  apply PeanoNat.Nat.lt_asymm in HOFS1.
  apply PeanoNat.Nat.lt_asymm in HOFS2.
  rewrite <- PeanoNat.Nat.ltb_nlt in HOFS1, HOFS2.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HOFS2, HNEQ1, HNEQ2.
    simpl.
    rewrite orb_false_r.
    rewrite andb_false_r.
    simpl.
    rewrite HALIVE1, HALIVE2. reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = block size & 0 < o2 < block size
          & two blocks are still alive,
     icmp eq ptr1, ptr2 is false.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_false2:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 = Ir.MemBlock.n mb1) (* o1 is the block size *)
         (HOFS2:0 < o2 < Ir.MemBlock.n mb2) (* 0 < o2 < block size *)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, None)) (* the blocks are alive *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, None))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)).
Proof.
  intros.
  assert (HNEQ2: o2 <> Ir.MemBlock.n mb2). omega.
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  apply <- PeanoNat.Nat.eqb_eq in HOFS1.
  destruct HOFS2 as [HOFS21 HOFS22].
  apply Nat.lt_neq in HOFS21.
  apply not_eq_sym in HOFS21.
  rewrite <- Nat.eqb_neq in HOFS21.
  apply PeanoNat.Nat.lt_asymm in HOFS22.
  rewrite <- PeanoNat.Nat.ltb_nlt in HOFS22.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HOFS21, HOFS22, HNEQ2.
    simpl.
    rewrite orb_false_r.
    rewrite andb_false_r.
    simpl.
    rewrite HALIVE1, HALIVE2.
    rewrite PeanoNat.Nat.eqb_eq in HOFS1.
    rewrite HOFS1.
    rewrite Nat.ltb_irrefl.
    reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & two blocks have disjoint life times,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_nondet1:
  forall st r rty op1 op2 sr md l1 l2 o1 o2 mb1 mb2 beg1 beg2 end1 end2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HALIVE1:Ir.MemBlock.r mb1 = (beg1, Some end1)) (* blocks' life times *)
         (HALIVE2:Ir.MemBlock.r mb2 = (beg2, Some end2))
         (HDISJ: end1 <= beg2 \/ end2 <= beg1) (* life times are disjoint. *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Stack.empty (Ir.Config.s st)=false), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1) 
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    simpl.
    rewrite HALIVE1, HALIVE2.
    inv HDISJ; rewrite <- PeanoNat.Nat.leb_le in H; rewrite H.
    simpl. repeat (rewrite orb_true_r). reflexivity.
    simpl. repeat (rewrite orb_true_r). reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      {
        assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (S res))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = 0 & o2 = block size,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_nondet2:
  forall st r rty op1 op2 sr md l1 l2 o2 mb1 mb2
         (HWF:Ir.Config.wf md st) (* The input state is well-formed *)
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 0)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS2:o2 = Ir.MemBlock.n mb2) (* o2 is the block size *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Stack.empty (Ir.Config.s st)=false), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  assert (HNEQ1: 0 <> Ir.MemBlock.n mb1).
  { (* Prove this from well-formedness of block mb1. *)
    inv HWF. inv wf_m.
    symmetry in HBLK1.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st)) in HBLK1.
    apply wf_blocks in HBLK1.
    inv HBLK1.
    unfold no_empty_range in wf_poslen.
    unfold Ir.MemBlock.P_ranges in wf_poslen.
    destruct (Ir.MemBlock.n mb1) eqn:HN.
    { induction (Ir.MemBlock.P mb1).
      { simpl in wf_twin. inv wf_twin. }
      { simpl in wf_poslen. congruence. }
    }
    { omega. }
    { reflexivity. }
  } 
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ1.
  rewrite <- PeanoNat.Nat.eqb_eq in HOFS2.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 0)
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS2, HNEQ1.
    simpl.
    reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (S res))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
          & l1 != l2
          & o1 = block size & o2 = 0,
  icmp eq ptr1, ptr2 yields nondeterminstic result.
 ****************************************************)

Theorem icmp_eq_ptr_diffblock_nondet3:
  forall st r rty op1 op2 sr md l1 l2 o1 mb1 mb2
         (HWF:Ir.Config.wf md st) (* The input state is well-formed *)
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 0)))
         (HDIFFBLK:l1 <> l2) (* different memory blocks *)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_eq r rty op1 op2))
         (HBLK1:Ir.Memory.get (Ir.Config.m st) l1 = Some mb1)
         (HBLK2:Ir.Memory.get (Ir.Config.m st) l2 = Some mb2)
         (HOFS1:o1 = Ir.MemBlock.n mb1) (* o2 is the block size *)
         (HINST:Ir.SmallStep.inst_step md st sr)
         (HNONEMPTYSTACK:Ir.Stack.empty (Ir.Config.s st)=false), (* register file should exist *)
    exists sr2,
      Ir.SmallStep.inst_step md st sr2 /\
      sr <> sr2.
Proof.
  intros.
  assert (HNEQ2: 0 <> Ir.MemBlock.n mb2).
  { (* Prove this from well-formedness of block mb1. *)
    inv HWF. inv wf_m.
    symmetry in HBLK2.
    apply Ir.Memory.get_In with (blks := Ir.Memory.blocks (Ir.Config.m st)) in HBLK2.
    apply wf_blocks in HBLK2.
    inv HBLK2.
    unfold no_empty_range in wf_poslen.
    unfold Ir.MemBlock.P_ranges in wf_poslen.
    destruct (Ir.MemBlock.n mb2) eqn:HN.
    { induction (Ir.MemBlock.P mb2).
      { simpl in wf_twin. inv wf_twin. }
      { simpl in wf_poslen. congruence. }
    }
    { omega. }
    { reflexivity. }
  }
  rewrite <- PeanoNat.Nat.eqb_neq in HNEQ2.
  rewrite <- PeanoNat.Nat.eqb_eq in HOFS1.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.

  assert (HNONDET:Ir.SmallStep.icmp_eq_ptr_nondet_cond (Ir.plog l1 o1)
                (Ir.plog l2 0) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_eq_ptr_nondet_cond.
    rewrite HBLK1, HBLK2, HDIFFBLK.
    rewrite HOFS1, HNEQ2.
    simpl.
    reflexivity.
  }

  inv HINST; try congruence.
  - (* it's not deterministic. *)
    unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_eq_ptr in HNEXT.
    rewrite HDIFFBLK in HNEXT.
    rewrite HNONDET in HNEXT. congruence.
  - destruct res.
    {
      exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 1))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
               (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_eq_nondet.
        eassumption. reflexivity. eassumption. eassumption.
        eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num (S res))) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r0 (Ir.num 0))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval. congruence. assumption. }
        congruence.
      }
    }
Qed.

End IcmpEq.



Module IcmpUle.

(****************************************************
            icmp ule 1, 2 is always true.
 ****************************************************)

Theorem icmp_ule_int_true1:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 1))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 2))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule 15, 15 is always true.
 ****************************************************)

Theorem icmp_ule_int_true2:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 15))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := true *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule 15, 14 is always false.
 ****************************************************)

Theorem icmp_ule_int_false:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 15))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.num 14))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := false *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
            icmp ule poison, _ is always poison.
 ****************************************************)

Theorem icmp_ule_poison:
  forall st r rty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1 in HNEXT. inv HNEXT.
  reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
       & o1 <= block size & o2 <= block size,
     icmp ule ptr1, ptr2 is equivalent to o1 <= o2.
 ****************************************************)

Theorem icmp_ule_ptr_sameblock_det:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb)
         (HOFS1:o1 <= Ir.MemBlock.n mb)
         (HOFS2:o2 <= Ir.MemBlock.n mb)
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := o1 <= o2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r
                                               (Ir.SmallStep.to_num (Nat.leb o1 o2))).
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l o1)
                (Ir.plog l o2) (Ir.Config.m st) = false).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite HBLK.
    rewrite <- PeanoNat.Nat.leb_le in HOFS1, HOFS2.
    rewrite HOFS1. rewrite HOFS2. reflexivity. }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    rewrite HBLK in HNEXT.
    inv HNEXT.
    reflexivity.
Qed.

(****************************************************
       If ptr1 = log(l, o1) & ptr2 = log(l, o2),
       & (block size < o1 \/ block size < o2),
  icmp ule ptr1, ptr2 yields nondeterministic value.
 ****************************************************)

Theorem icmp_ule_ptr_sameblock_nondet:
  forall st r rty op1 op2 sr md l o1 o2 mb
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l o2)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l = Some mb)
         (HOFS:Ir.MemBlock.n mb < o1 \/ Ir.MemBlock.n mb < o2)
         (HNONEMPTYSTACK:Ir.Stack.empty (Ir.Config.s st)=false) (* register file should exist *)
         (HINST:Ir.SmallStep.inst_step md st sr),
    exists sr',
      Ir.SmallStep.inst_step md st sr' /\
      sr' <> sr.
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l o1)
                (Ir.plog l o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite HBLK.
    repeat (rewrite Nat.lt_nge in HOFS).
    repeat (rewrite <- Nat.leb_nle in HOFS).
    destruct HOFS.
    { rewrite H. reflexivity. }
    { rewrite H. simpl. rewrite orb_true_r. reflexivity. }
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    inv HNEXT.
  - rewrite HCUR in HCUR0.
    inv HCUR0.
    destruct res.
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num (S res)))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }   
Qed.

(****************************************************
       If ptr1 = log(l1, o1) & ptr2 = log(l2, o2),
  icmp ule ptr1, ptr2 yields nondeterministic value.
 ****************************************************)

Theorem icmp_ule_ptr_diffblock_nondet:
  forall st r rty op1 op2 sr md l1 l2 o1 o2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.iicmp_ule r rty op1 op2))
         (HNONEMPTYSTACK:Ir.Stack.empty (Ir.Config.s st)=false) (* register file should exist *)
         (HINST:Ir.SmallStep.inst_step md st sr),
    exists sr',
      Ir.SmallStep.inst_step md st sr' /\
      sr' <> sr.
Proof.
  intros.
  assert (HNONDET: Ir.SmallStep.icmp_ule_ptr_nondet_cond (Ir.plog l1 o1)
                (Ir.plog l2 o2) (Ir.Config.m st) = true).
  { unfold Ir.SmallStep.icmp_ule_ptr_nondet_cond.
    rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.
    rewrite HDIFFBLK. reflexivity.
  }

  inv HINST; try congruence.
  - unfold Ir.SmallStep.inst_det_step in HNEXT.
    rewrite HCUR in HNEXT.
    rewrite HOP1, HOP2 in HNEXT.
    unfold Ir.SmallStep.icmp_ule_ptr in HNEXT.
    rewrite HNONDET in HNEXT.
    inv HNEXT.
  - rewrite HCUR in HCUR0.
    inv HCUR0.
    destruct res.
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }
    { exists (Ir.SmallStep.sr_success Ir.e_none
      (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0))).
      split.
      { eapply Ir.SmallStep.s_icmp_ule_nondet.
        rewrite HCUR. reflexivity. reflexivity. eassumption.
        eassumption. eassumption. }
      { assert ((Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 0)) <>
                (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num (S res)))).
        { apply Ir.SmallStep.update_reg_and_incrpc_diffval.
          congruence. assumption. }
        congruence.
      }
    }   
Qed.

End IcmpUle.



Module PSub.

(****************************************************
            psub poison, _ is always poison.
 ****************************************************)

Theorem psub_poison:
  forall st r rty pty op1 op2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r rty pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1 in HNEXT. inv HNEXT.
  des_ifs.
Qed.

(****************************************************
     If ptr1 = log(l, 10) & ptr2 = log(l, 9),
      psub i8 ptr1, ptr2 = 1.
      (i8 means the return value is truncated
       into 8 bits)
 ****************************************************)

Theorem psub_sameblock1:
  forall st r pty op1 op2 l sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l 10)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l 9)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r (Ir.ity 8) pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 1 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 1)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite Ir.PTRSZ_def.
  des_ifs.
Qed.

(****************************************************
     If ptr1 = log(l, 10) & ptr2 = log(l, 11),
      psub i8 ptr1, ptr2 = 255.
      (i8 means the return value is truncated
       into 8 bits)
 ****************************************************)

Theorem psub_sameblock2:
  forall st r pty op1 op2 l sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l 10)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l 11)))
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r (Ir.ity 8) pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 255 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 255)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  unfold Ir.SmallStep.twos_compl_sub.
  unfold Ir.SmallStep.twos_compl.
  rewrite PeanoNat.Nat.eqb_refl.
  rewrite Ir.PTRSZ_def.
  des_ifs.
Qed.

(****************************************************
     If ptr1 = log(l1, o1) & ptr2 = log(l2, o2)
        & l1 <> l2,
      psub ptr1, ptr2 = poison.
 ****************************************************)

Theorem psub_diffblock:
  forall st r retty pty op1 op2 l1 o1 l2 o2 sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 o1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.plog l2 o2)))
         (HDIFFBLK:l1 <> l2)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r retty pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.poison)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  rewrite <- PeanoNat.Nat.eqb_neq in HDIFFBLK.
  rewrite HDIFFBLK.
  des_ifs.
Qed.

(****************************************************
     If ptr1 = log(l1, 10) & ptr2 = phy(128, _, _)
        & addr(l1) = 138,
      psub ptr1, ptr2 = 138 + 10 - 128 = 20.
 ****************************************************)

Theorem psub_log_phy:
  forall st r pty op1 op2 l1 sr md I cid blk
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 10)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.pphy 128 I cid)))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l1 = Some blk)
         (HADDR:Ir.MemBlock.addr blk = 138)
         (HCUR:Ir.Config.cur_inst md st = Some (Ir.Inst.ipsub r (Ir.ity 8) pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 20 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 20)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  unfold Ir.SmallStep.twos_compl_sub.
  unfold Ir.SmallStep.twos_compl.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  rewrite HBLK.
  rewrite HADDR.
  rewrite Nat.min_id.
  rewrite Ir.PTRSZ_MEMSZ.
  unfold Ir.SmallStep.twos_compl.
  rewrite Ir.PTRSZ_MEMSZ.
  rewrite Nat.mod_mod.
  replace ((((138 + 10) mod Ir.MEMSZ + Ir.MEMSZ - 128) mod Ir.MEMSZ)
             mod Nat.shiftl 2 (8 - 1)) with 20.
  ss.
  unfold Ir.MEMSZ. rewrite Ir.PTRSZ_def. reflexivity.
  pose Ir.MEMSZ_pos. omega.
Qed.

(****************************************************
     If ptr1 = log(l1, 1) & ptr2 = phy(8, _, _)
        & addr(l1) = 4,
  psub i4 ptr1, ptr2 = (4 + 1 - 8) % 16 = 13.
 ****************************************************)

Theorem psub_log_phy2:
  forall st r pty op1 op2 l1 sr md I cid blk
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.plog l1 1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.pphy 8 I cid)))
         (HBLK:Ir.Memory.get (Ir.Config.m st) l1 = Some blk)
         (HADDR:Ir.MemBlock.addr blk = 4)
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.ipsub r (Ir.ity 4) pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 13 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 13)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  unfold Ir.SmallStep.twos_compl_sub.
  unfold Ir.SmallStep.twos_compl.
  unfold Ir.SmallStep.p2N.
  unfold Ir.log_to_phy.
  rewrite HBLK.
  rewrite HADDR.
  rewrite Ir.PTRSZ_def.
  des_ifs.
  replace (((Ir.SmallStep.twos_compl ((4 + 1) mod Ir.MEMSZ) (Nat.min 16 16) +
             Nat.shiftl 2 (16 - 1) - 8) mod Nat.shiftl 2 (16 - 1))
           mod Nat.shiftl 2 (4 - 1)) with 13.
  ss.
  unfold Ir.MEMSZ. rewrite Nat.min_id.
  rewrite Ir.PTRSZ_def.
  reflexivity.
Qed.

(****************************************************
     If ptr1 = phy(10, _, _) & ptr2 = phy(8, _, _)
              psub i4 ptr1, ptr2 = 2
 ****************************************************)

Theorem psub_phy_phy:
  forall st r pty op1 op2 sr md I1 I2 cid1 cid2
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.ptr (Ir.pphy 10 I1 cid1)))
         (HOP2:Ir.Config.get_val st op2 = Some (Ir.ptr (Ir.pphy 8 I2 cid2)))
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.ipsub r (Ir.ity 4) pty op1 op2))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 2)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR in HNEXT.
  rewrite HOP1, HOP2 in HNEXT.
  inv HNEXT.
  unfold Ir.SmallStep.psub.
  unfold Ir.SmallStep.twos_compl_sub.
  unfold Ir.SmallStep.twos_compl.
  unfold Ir.SmallStep.p2N.
  rewrite Ir.PTRSZ_def.
  replace (((10 + Nat.shiftl 2 (16 - 1) - 8) mod Nat.shiftl 2 (16 - 1))
           mod Nat.shiftl 2 (4 - 1)) with 2.
  ss.
  reflexivity.
Qed.


End PSub.


Module Freeze.

(****************************************************
               freeze poison is an integer.
 ****************************************************)

Theorem freeze_poison:
  forall st op1 r sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.poison))
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.ifreeze r op1 (Ir.ity 4)))
         (HINST:Ir.SmallStep.inst_step md st sr),
    exists i,
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := int *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num i)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOP1 in HNEXT.
  inv HNEXT.
  rewrite HCUR in HCUR0. inv HCUR0.
  eexists.  ss.
Qed.

(****************************************************
               freeze 10 is 10.
 ****************************************************)

Theorem freeze_10:
  forall st op1 r sr md
         (HOP1:Ir.Config.get_val st op1 = Some (Ir.num 10))
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.ifreeze r op1 (Ir.ity 4)))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := 2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r (Ir.num 10)).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOP1 in HNEXT.
  inv HNEXT. ss.
Qed.

End Freeze.


Module Select.

(****************************************************
            select poison, _, _ is poison.
 ****************************************************)

Theorem select_poison:
  forall st opcond op1 op2 r sr md v1 v2 condty opty
         (HOPCOND:Ir.Config.get_val st opcond = Some (Ir.poison))
         (HOP1:Ir.Config.get_val st op1 = Some v1)
         (HOP2:Ir.Config.get_val st op2 = Some v2)
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.iselect r opcond condty op1 op2 opty))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := poison *)
           (Ir.SmallStep.update_reg_and_incrpc md st r Ir.poison).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOPCOND in HNEXT.
  inv HNEXT. ss.
Qed.

(****************************************************
            select 1, x, _ is x.
 ****************************************************)

Theorem select_first:
  forall st opcond op1 op2 r sr md v1 v2 condty opty
         (HOPCOND:Ir.Config.get_val st opcond = Some (Ir.num 1))
         (HOP1:Ir.Config.get_val st op1 = Some v1)
         (HOP2:Ir.Config.get_val st op2 = Some v2)
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.iselect r opcond condty op1 op2 opty))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := v1 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r v1).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOPCOND, HOP1, HOP2 in HNEXT.
  inv HNEXT. ss.
Qed.

(****************************************************
            select 0, _, y is y.
 ****************************************************)

Theorem select_second:
  forall st opcond op1 op2 r sr md v1 v2 condty opty
         (HOPCOND:Ir.Config.get_val st opcond = Some (Ir.num 0))
         (HOP1:Ir.Config.get_val st op1 = Some v1)
         (HOP2:Ir.Config.get_val st op2 = Some v2)
         (HCUR:Ir.Config.cur_inst md st =
               Some (Ir.Inst.iselect r opcond condty op1 op2 opty))
         (HINST:Ir.SmallStep.inst_step md st sr),
    sr = Ir.SmallStep.sr_success
           Ir.e_none (* no event *)
           (* new state, with PC incremented & r := v2 *)
           (Ir.SmallStep.update_reg_and_incrpc md st r v2).
Proof.
  intros.
  inv HINST; try congruence.
  unfold Ir.SmallStep.inst_det_step in HNEXT.
  rewrite HCUR, HOPCOND, HOP1, HOP2 in HNEXT.
  inv HNEXT. ss.
Qed.

End Select.

End SmallStepTest.

End Ir.

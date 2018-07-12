Require Import Bool.
Require Import BinNat.
Require Import sflib.
Require Import Omega.
Require Import Permutation.

Require Import Common.
Require Import Lang.
Require Import Value.
Require Import Behaviors.
Require Import Memory.
Require Import State.
Require Import SmallStep.


Module Ir.

Definition twin_state (st1 st2:Ir.Config.t) (blkid:Ir.blockid) :=
  Ir.Config.eq_wom st1 st2 /\
  exists mb1 mb2,
    Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid /\
    Some mb2 = Ir.Memory.get (Ir.Config.m st2) blkid /\
    (Ir.MemBlock.bt mb1) = (Ir.MemBlock.bt mb2) /\
    (Ir.MemBlock.r mb1) = (Ir.MemBlock.r mb2) /\
    (Ir.MemBlock.n mb1) = (Ir.MemBlock.n mb2) /\
    (Ir.MemBlock.a mb1) = (Ir.MemBlock.a mb2) /\
    (Ir.MemBlock.c mb1) = (Ir.MemBlock.c mb2) /\
    Permutation (Ir.MemBlock.P mb1) (Ir.MemBlock.P mb2) /\
    Ir.MemBlock.P mb1 <> Ir.MemBlock.P mb2.

(* Definition of a 'twin' step. *)
Inductive twin_step:
Ir.SmallStep.step_res -> Ir.SmallStep.step_res -> Ir.blockid -> Prop :=
  | ts_success:
      forall st1 st2 (sr1 sr2:Ir.SmallStep.step_res) (e1 e2:Ir.event) blkid
             (HSR1:sr1 = Ir.SmallStep.sr_success e1 st1)
             (HSR2:sr2 = Ir.SmallStep.sr_success e2 st2)
             (HTWIN:twin_state st1 st2 blkid),
        twin_step sr1 sr2 blkid
  | ts_goes_wrong:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_goes_wrong)
             (HSR1:sr2 = Ir.SmallStep.sr_goes_wrong),
        twin_step sr1 sr2 blkid
  | ts_oom:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_oom)
             (HSR1:sr2 = Ir.SmallStep.sr_oom),
        twin_step sr1 sr2 blkid
  | ts_prog_finish:
      forall sr1 sr2 blkid v
             (HSR1:sr1 = Ir.SmallStep.sr_prog_finish v)
             (HSR1:sr2 = Ir.SmallStep.sr_prog_finish v),
        twin_step sr1 sr2 blkid.


Inductive observes_block (md:Ir.IRModule.t) (st:Ir.Config.t) (blkid:Ir.blockid):Prop :=
  | ob_by_ptrtoint:
      forall r op1 retty o
             (HINST:Some (Ir.Inst.iptrtoint r op1 retty) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1),
        observes_block md st blkid
  | ob_by_iicmpeq_l:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_eq r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_iicmpeq_r:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_eq r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid
  | ob_by_iicmpule_l:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_ule r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_iicmpule_r:
      forall r op1 op2 opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.iicmp_ule r opty op1 op2) = Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid
  | ob_by_psub_l:
      forall r op1 op2 retty opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.ipsub r retty opty op1 op2) =
                    Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op1)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op2), 
        observes_block md st blkid
  | ob_by_psub_r:
      forall r op1 op2 retty opty o o2 I2 cid2
             (HINST:Some (Ir.Inst.ipsub r retty opty op1 op2) =
                    Ir.Config.cur_inst md st)
             (HOP1:Some (Ir.ptr (Ir.plog blkid o)) = Ir.Config.get_val st op2)
             (HOP2:Some (Ir.ptr (Ir.pphy o2 I2 cid2)) = Ir.Config.get_val st op1), 
        observes_block md st blkid.


Theorem twin_property:
  forall (md:Ir.IRModule.t) (blkid:Ir.blockid)
    (HNEVER_OBSERVED: forall (st:Ir.Config.t), ~ observes_block md st blkid),
    forall (st1 st2:Ir.Config.t) (sr1 sr2:Ir.SmallStep.step_res)
           (HTWIN:twin_state st1 st2 blkid)
           (HSTEP1:Ir.SmallStep.inst_step md st1 sr1)
           (HSTEP2:Ir.SmallStep.inst_step md st2 sr2),
      twin_step sr1 sr2 blkid.
Proof.
Qed.

Definition

End Ir.
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
Require Import WellTyped.
Require Import LoadStore.
Require Import SmallStep.
Require Import Reordering.

(***********************************************************
  TwinExecution.v / TwinExecutionProof.v formalizes
  Sec. 4.11 - twin allocation prevents accesses via guessed
  addresses.
 ***********************************************************)

Module Ir.

(* Definition of 'twin' states.*)
Definition twin_state (st1 st2:Ir.Config.t) (blkid:Ir.blockid):Prop :=
  Ir.Config.eq_wom st1 st2 /\
  Ir.Memory.mt (Ir.Config.m st1) = Ir.Memory.mt (Ir.Config.m st2) /\
  Ir.Memory.calltimes (Ir.Config.m st1) = Ir.Memory.calltimes (Ir.Config.m st2) /\
  Ir.Memory.fresh_bid (Ir.Config.m st1) = Ir.Memory.fresh_bid (Ir.Config.m st2) /\
  forall bid',
    (forall (HMATCH:bid' = blkid),
        exists mb1 mb2,
          Some mb1 = Ir.Memory.get (Ir.Config.m st1) blkid /\
          Some mb2 = Ir.Memory.get (Ir.Config.m st2) blkid /\
          (Ir.MemBlock.bt mb1) = (Ir.MemBlock.bt mb2) /\
          (Ir.MemBlock.r mb1) = (Ir.MemBlock.r mb2) /\
          (Ir.MemBlock.n mb1) = (Ir.MemBlock.n mb2) /\
          (Ir.MemBlock.a mb1) = (Ir.MemBlock.a mb2) /\
          (Ir.MemBlock.c mb1) = (Ir.MemBlock.c mb2) /\
          Permutation (Ir.MemBlock.P mb1) (Ir.MemBlock.P mb2) /\
          List.hd 0 (Ir.MemBlock.P mb1) <> List.hd 0 (Ir.MemBlock.P mb2))
    /\
    (forall (HMATCH:bid' <> blkid),
        Ir.Memory.get (Ir.Config.m st1) bid' =
        Ir.Memory.get (Ir.Config.m st2) bid').

(* Given two small step results (e.g. success/goes wrong/oom/program end),
   they are twin if it satisfies one of the followings. *)
Inductive twin_sresult:
Ir.SmallStep.step_res -> Ir.SmallStep.step_res -> Ir.blockid -> Prop :=
  | ts_success:
      forall st1 st2 (sr1 sr2:Ir.SmallStep.step_res) (e1 e2:Ir.event) blkid
             (HSR1:sr1 = Ir.SmallStep.sr_success e1 st1)
             (HSR2:sr2 = Ir.SmallStep.sr_success e2 st2)
             (HEVENT:e1 = e2)
             (HTWIN:twin_state st1 st2 blkid),
        twin_sresult sr1 sr2 blkid
  | ts_goes_wrong:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_goes_wrong)
             (HSR1:sr2 = Ir.SmallStep.sr_goes_wrong),
        twin_sresult sr1 sr2 blkid
  | ts_oom:
      forall sr1 sr2 blkid
             (HSR1:sr1 = Ir.SmallStep.sr_oom)
             (HSR1:sr2 = Ir.SmallStep.sr_oom),
        twin_sresult sr1 sr2 blkid
  | ts_prog_finish:
      forall sr1 sr2 blkid v1 v2
             (* Note that there's no constraint on v1 and v2.
                prog_finish means that the function is returned with a
                return value. However we don't know what the caller will
                do with the returned value. For example, if the caller
                has no ptrtoint/icmp/.. instructions, twin-stateness will
                still preserve.
                To embrace such case, there's no condition for return values here. *)
             (HSR1:sr1 = Ir.SmallStep.sr_prog_finish v1)
             (HSR1:sr2 = Ir.SmallStep.sr_prog_finish v2),
        twin_sresult sr1 sr2 blkid.

(* A memory block blkid is observed at state st if.. *)
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

(* A value is possibly a guessed pointer if it is a physical pointer. *)
Inductive possibly_guessedptr (v:Ir.val):Prop :=
| pg_phy: forall o I cid (HPHY: v = Ir.ptr (Ir.pphy o I cid)),
    possibly_guessedptr v.

(* Memory access from a possibly guessed pointer if.. *)
Inductive memaccess_from_possibly_guessedptr (md:Ir.IRModule.t) (st:Ir.Config.t)
:Prop :=
  | gp_store:
      forall valty opval opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.istore valty opptr opval) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st
  | gp_load:
      forall retty opval opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.iload retty opval opptr) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st
  | gp_free:
      forall opptr vptr
        (HOPPTR: Some vptr = Ir.Config.get_val st opptr)
        (HGUESSED: possibly_guessedptr vptr)
        (HINST: Some (Ir.Inst.ifree opptr) =
                Ir.Config.cur_inst md st),
        memaccess_from_possibly_guessedptr md st.

(* Does current instruction dereference blkid? *)
Definition inst_derefs md (st:Ir.Config.t) (blkid:Ir.blockid): bool :=
  match (Ir.Config.cur_inst md st) with
  | Some i =>
    match i with
    | Ir.Inst.iload _ retty opp =>
      match Ir.Config.get_val st opp with
      | Some (Ir.ptr opp) =>
        List.existsb (fun itm => blkid =? itm.(fst).(fst))
                          (Ir.get_deref (Ir.Config.m st) opp (Ir.ty_bytesz retty))
      | _ => false
      end
    | Ir.Inst.istore valty opp _ =>
      match Ir.Config.get_val st opp with
      | Some (Ir.ptr opp) =>
        List.existsb (fun itm => blkid =? itm.(fst).(fst))
                          (Ir.get_deref (Ir.Config.m st) opp (Ir.ty_bytesz valty))
      | _ => false
      end
    | Ir.Inst.ifree opp =>
      match Ir.Config.get_val st opp with
      | Some (Ir.ptr opp) =>
        List.existsb (fun itm =>blkid =? itm.(fst).(fst))
                (Ir.get_deref (Ir.Config.m st) opp 1)
      | _ => false
      end
    | _ => false
    end
  | None => false
  end.



End Ir.
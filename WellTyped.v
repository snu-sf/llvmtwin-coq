Require Import Common.
Require Import List.
Require Import sflib.

Require Import Value.
Require Import Lang.
Require Import State.

Module Ir.

Inductive inst_typechecked (md:Ir.IRModule.t) (st:Ir.Config.t)
:Prop :=
| tc_bop:
    forall op1 op2 r opty bopc i1 i2 bsz
           (HINST: Some (Ir.Inst.ibinop r opty bopc op1 op2) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ity bsz = opty)
           (HOP1: Some (Ir.num i1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.num i2) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_psub:
    forall op1 op2 r retty ptrty p1 p2 bsz pty
           (HINST: Some (Ir.Inst.ipsub r retty ptrty op1 op2) =
                Ir.Config.cur_inst md st)
           (HRETTY: Ir.ity bsz = retty)
           (HPTY: Ir.ptrty pty = ptrty)
           (HOP1: Some (Ir.ptr p1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.ptr p2) = Ir.Config.get_val st op1),
        inst_typechecked md st
| tc_gep:
    forall op1 op2 r ptrty p i pty inb
           (HINST: Some (Ir.Inst.igep r ptrty op1 op2 inb) =
                Ir.Config.cur_inst md st)
           (HPTY: Ir.ptrty pty = ptrty)
           (HOP1: Some (Ir.ptr p) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.num i) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_load:
    forall retty opval opptr p
        (HINST: Some (Ir.Inst.iload retty opval opptr) =
                Ir.Config.cur_inst md st)
        (HOPPTR: Some (Ir.ptr p) = Ir.Config.get_val st opptr),
        inst_typechecked md st
| tc_store:
    forall valty opval opptr p v
           (HINST: Some (Ir.Inst.istore valty opptr opval) =
                Ir.Config.cur_inst md st)
           (HOPPTR: Some (Ir.ptr p) = Ir.Config.get_val st opptr)
           (HOPVAL: Some v = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_malloc:
    forall opty opval i sz r
           (HINST: Some (Ir.Inst.imalloc r opty opval) =
                Ir.Config.cur_inst md st)
           (HOPPTR: Some (Ir.num i) = Ir.Config.get_val st opval)
           (HSZTY: Ir.ity sz = opty),
        inst_typechecked md st
| tc_bitcast_int:
    forall r opval retty bsz i1
           (HINST: Some (Ir.Inst.ibitcast r opval retty) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ity bsz = retty)
           (HOP1: Some (Ir.num i1) = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_bitcast_ptr:
    forall r opval retty pty p
           (HINST: Some (Ir.Inst.ibitcast r opval retty) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ptrty pty = retty)
           (HOP1: Some (Ir.ptr p) = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_ptrtoint:
    forall r opval retty bsz p
           (HINST: Some (Ir.Inst.iptrtoint r opval retty) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ity bsz = retty)
           (HOP1: Some (Ir.ptr p) = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_inttoptr:
    forall r opval retty pty i
           (HINST: Some (Ir.Inst.iinttoptr r opval retty) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ptrty pty = retty)
           (HOP1: Some (Ir.num i) = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_event:
    forall opval i
           (HINST: Some (Ir.Inst.ievent opval) =
                Ir.Config.cur_inst md st)
           (HOP1: Some (Ir.num i) = Ir.Config.get_val st opval),
        inst_typechecked md st
| tc_icmpeq_int:
    forall op1 op2 r opty i1 i2 bsz
           (HINST: Some (Ir.Inst.iicmp_eq r opty op1 op2) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ity bsz = opty)
           (HOP1: Some (Ir.num i1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.num i2) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_icmpeq_ptr:
    forall op1 op2 r opty p1 p2 pty
           (HINST: Some (Ir.Inst.iicmp_eq r opty op1 op2) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ptrty pty = opty)
           (HOP1: Some (Ir.ptr p1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.ptr p2) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_icmpule_int:
    forall op1 op2 r opty i1 i2 bsz
           (HINST: Some (Ir.Inst.iicmp_ule r opty op1 op2) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ity bsz = opty)
           (HOP1: Some (Ir.num i1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.num i2) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_icmpule_ptr:
    forall op1 op2 r opty p1 p2 pty
           (HINST: Some (Ir.Inst.iicmp_ule r opty op1 op2) =
                Ir.Config.cur_inst md st)
           (HTY: Ir.ptrty pty = opty)
           (HOP1: Some (Ir.ptr p1) = Ir.Config.get_val st op1)
           (HOP2: Some (Ir.ptr p2) = Ir.Config.get_val st op2),
        inst_typechecked md st
| tc_free:
    forall opptr p
        (HINST: Some (Ir.Inst.ifree opptr) =
                Ir.Config.cur_inst md st)
        (HOPPTR: Some (Ir.ptr p) = Ir.Config.get_val st opptr),
        inst_typechecked md st.


(****************************************
        Dominatedness relation.
 ***************************************)

Definition dominates (from to:Ir.IRFunction.pc) (f:Ir.IRFunction.t) :=
  forall (exec:list Ir.IRFunction.pc)
         (HLEN:List.length exec > 0)
         (HBEGIN:List.hd from exec = Ir.IRFunction.get_begin_pc f)
         (HEND:List.last exec to = to)
         (HVALID: forall_adj
                    (fun pc pc_next => Ir.IRFunction.valid_next_pc pc pc_next f)
                    exec = true),
    List.In from exec.

(* Theorem: reflexivity of dominatedness. *)
Theorem dominates_refl:
  forall (pc:Ir.IRFunction.pc) (f:Ir.IRFunction.t),
    dominates pc pc f.
Proof.
  intros.
  unfold dominates.
  intros.
  destruct exec.
  simpl in HLEN. inversion HLEN.
  simpl in HBEGIN.

  apply last_head in HEND.
  remember (rev (p::exec)) as l.
  assert (List.length l = List.length (p::exec)).
  { rewrite Heql. rewrite rev_length. reflexivity. }
  destruct l.
  - simpl in H. inversion H.
  - simpl in HEND.
    assert (p :: exec = rev (p0::l)).
    { rewrite Heql. rewrite rev_involutive. reflexivity. }
    rewrite H0.
    apply in_rev. rewrite rev_involutive. rewrite HEND. constructor.
    reflexivity.
  - simpl.
    apply Gt.gt_Sn_O.
Qed.


End Ir.
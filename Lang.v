Require Import List.
Require Import BinPos.
Require Import sflib.
Require Import Bool.

Require Import Common.
Require Import Memory.
Require Import Omega.


Module Ir.

Inductive ty :=
| ity: nat -> ty (* bitsz *)
| ptrty: ty -> ty.

Definition ty_bitsz (t:ty):nat :=
  match t with
  | ity bitsz =>
    match bitsz with
    | 0 => 1 (* no 'zero-bit' sized integer, thanks to type checking *)
    | _ => bitsz
    end
  | ptrty _ => Ir.PTRSZ
  end.

Definition ty_bytesz (t:ty):nat :=
  Nat.div (7 + ty_bitsz t) 8.

Inductive const :=
| cnum: ty -> nat -> const
| cnullptr: ty -> const
| cpoison: ty -> const
| cglb: nat -> const.

Definition reg := nat.

Inductive op :=
| opconst: const -> op
| opreg: reg -> op.

Definition regop (o:op): list reg :=
  match o with
  | opreg r => r::nil
  | _ => nil
  end.



Lemma ty_bytesz_pos:
  forall t, Ir.ty_bytesz t > 0.
Proof.
  intros.
  unfold Ir.ty_bytesz.
  destruct t.
  { destruct n.
    { simpl. omega. }
    { unfold Ir.ty_bitsz.
      assert (lt_gt:   forall n1 n2, n1 < n2 -> n2 > n1).
      { intros. omega. }
      apply lt_gt.
      rewrite Nat.div_str_pos_iff.
      omega.
      omega.
    }
  }
  { unfold Ir.ty_bitsz.
    rewrite Ir.PTRSZ_def. simpl. omega.
  }
Qed.



(* PHI Node. *)
Module PhiNode.

(* register, reg.type, (basicblock id, value) list *)
Definition t:Type := reg * ty * list (nat * op).

Definition regops (p:t): list reg :=
  List.concat (List.map regop (List.split p.(snd)).(snd)).

Definition def (p:t):reg * ty :=
  p.(fst).

End PhiNode.


(* Instructions (which will be in the body of a basic block. *)
Module Inst.

Inductive bopcode :=
| bop_add | bop_sub.

Inductive t :=
| ibinop: reg -> ty -> bopcode -> op -> op -> t (* lhs, retty, op1, op2 *)
| ifreeze: reg -> op -> ty -> t (* lhs, op, retty *)
| iselect: reg -> op -> ty -> op -> op -> ty -> t (* lhs, cond, condty, op1, op2, opty *)
| ipsub: reg -> ty -> ty -> op -> op -> t (* lhs, retty, ptrty, ptr1, ptr2 *)
| igep: reg -> ty -> op -> op -> bool -> t (* lhs, retty, ptr, idx, inbounds *)
                                           (* For simplicity, retty equals first operand ty *)
| iload: reg -> ty -> op -> t (* retty, ptr *)
| istore: ty -> op -> op -> t (* valty, ptr, val *)
| imalloc: reg -> ty -> op -> t (* block size ty, block size *)
| ifree: op -> t (* pointer *)
| ibitcast: reg -> op -> ty -> t (* lhs, val, retty *)
| iptrtoint: reg -> op -> ty -> t (* lhs, ptr, retty *)
| iinttoptr: reg -> op -> ty -> t (* rhs, int, retty *)
| ievent: op -> t
| iicmp_eq: reg -> ty -> op -> op -> t (* lhs, opty, op1, op2 *)
| iicmp_ule: reg -> ty -> op -> op -> t (* lhs, opty, op1, op2 *)
.

Definition ops (i:t) :=
  match i with
  | ibinop _ _ _ op1 op2 => op1::op2::nil
  | ifreeze _ op1 _ => op1::nil
  | iselect _ opcond _ op1 op2 _ => opcond::op1::op2::nil
  | ipsub _ _ _ op1 op2 => op1::op2::nil
  | igep _ _ op1 op2 _ => op1::op2::nil
  | iload _ _ op1 => op1::nil
  | istore _ op1 op2 => op1::op2::nil
  | imalloc _ _ op1 => op1::nil
  | ifree op1 => op1::nil
  | ibitcast _ op1 _ => op1::nil
  | iptrtoint _ op1 _ => op1::nil
  | iinttoptr _ op1 _ => op1::nil
  | ievent op1 => op1::nil
  | iicmp_eq _ _ op1 op2 => op1::op2::nil
  | iicmp_ule _ _ op1 op2 => op1::op2::nil
  end.

Definition regops (i:t) :=
  match i with
  | ibinop _ _ _ op1 op2 => (regop op1) ++ (regop op2)
  | ifreeze _ op1 _ => (regop op1)
  | iselect _ opcond _ op1 op2 _ => (regop opcond) ++ (regop op1) ++ (regop op2)
  | ipsub _ _ _ op1 op2 => (regop op1) ++ (regop op2)
  | igep _ _ op1 op2 _ => (regop op1) ++ (regop op2)
  | iload _ _ op1 => regop op1
  | istore _ op1 op2 => (regop op1) ++ (regop op2)
  | imalloc _ _ op1 => regop op1
  | ifree op1 => regop op1
  | ibitcast _ op1 _ => regop op1
  | iptrtoint _ op1 _ => regop op1
  | iinttoptr _ op1 _ => regop op1
  | ievent op1 => regop op1
  | iicmp_eq _ _ op1 op2 => (regop op1) ++ (regop op2)
  | iicmp_ule _ _ op1 op2 => (regop op1) ++ (regop op2)
  end.

Definition def (i:t): option (reg * ty) :=
  match i with
  | ibinop r t _ _ _ => Some (r, t)
  | ifreeze r _ t => Some (r, t)
  | iselect r _ _ _ _ t => Some (r, t)
  | ipsub r t _ _ _ => Some (r, t)
  | igep r t _ _ _ => Some (r, t)
  | iload r t _ => Some (r, t)
  | istore _ _ _ => None
  | imalloc r t _ => Some (r, t)
  | ifree _ => None
  | ibitcast r _ t => Some (r, t)
  | iptrtoint r _ t => Some (r, t)
  | iinttoptr r _ t => Some (r, t)
  | ievent _ => None
  | iicmp_eq r _ _ _ => Some (r, ity 1)
  | iicmp_ule r _ _ _ => Some (r, ity 1)
  end.

End Inst.


Module Terminator.

Inductive t :=
| tbr: nat -> t (* unconditional branch *)
| tbr_cond: op -> nat -> nat -> t
| tret: op -> t (* returning value, instruction *)
.

Definition regops (t:t) :=
  match t with
  | tbr _ => nil
  | tbr_cond op1 _ _ => regop op1
  | tret op1 => regop op1
  end.

Definition destination (t:t):list nat :=
  match t with
  | tbr n => n::nil
  | tbr_cond _ n1 n2 => n1::n2::nil
  | tret _ => nil
  end.

Definition has_dest (blockid:nat) (t:t):bool :=
  match t with
  | tbr n => Nat.eqb n blockid
  | tbr_cond _ n1 n2 => Nat.eqb n1 blockid || Nat.eqb n2 blockid
  | tret _ => false
  end.

End Terminator.



Module BasicBlock.

Structure t := mkBB
    {name:nat;
     phis:list PhiNode.t;
     insts:list Inst.t;
     term:Terminator.t}.

Definition valid_phi_idx (i:nat) (t:t): bool :=
  Nat.ltb i (List.length t.(phis)).

Definition valid_inst_idx (i:nat) (t:t): bool :=
  Nat.ltb i (List.length t.(insts)).

(* Returns defs of phis *)
Definition phi_defs (bb:t): list (nat * (reg * ty)) :=
  List.map (fun pn => (pn.(fst), PhiNode.def pn.(snd)))
           (number_list bb.(phis)).

(* Returns uses of register r in phis *)
Definition phi_uses (r:reg) (bb:t): list nat :=
  fst (List.split
         (List.filter
            (fun pn => List.existsb (fun r' => Nat.eqb r r')
                                    (PhiNode.regops pn.(snd)))
              (number_list bb.(phis)))).

(* Returns defs of instructions *)
Definition inst_defs (bb:t): list (nat * (reg * ty)) :=
  List.concat (
    List.map (fun i =>
                match (Inst.def i.(snd)) with
                | Some rt => (i.(fst), rt)::nil | None => nil
             end)
             (number_list bb.(insts))).

(* Returns uses of register r in instructions *)
Definition inst_uses (r:reg) (bb:t): list nat :=
  fst (List.split
         (List.filter
            (fun pn => List.existsb (fun r' => Nat.eqb r r')
                                    (Inst.regops pn.(snd)))
              (number_list bb.(insts)))).

(* Returns true if register r is used by the terminator *)
Definition terminator_uses (r:reg) (bb:t): bool :=
  List.existsb (fun r' => Nat.eqb r r') (Terminator.regops bb.(term)).

End BasicBlock.



Module IRFunction.

Structure t := mk
  {
    retty:ty;
    name:nat;
    args:list (ty * nat);
    body:list BasicBlock.t
  }.

Structure wf (fdef:t):= mk_wf
  {
    wf_nonempty: List.length (body fdef) > 0;
    wf_arg_nodup: List.NoDup (List.map snd (args fdef))
  }.


Definition getbb (bname:nat) (f:t): option BasicBlock.t :=
    match List.filter (fun b => Nat.eqb bname b.(BasicBlock.name)) f.(body) with
    | nil => None
    | h::t => Some h
    end.


(* program counter *)
Inductive pc:Type :=
| pc_phi (bbid:nat) (pidx:nat)
| pc_inst (bbid:nat) (iidx:nat).


(* Get PCs of definitions of register r.
   Note that, in SSA, the result of get_defs is singleton.
   This will be shown in WellTyped.v *)
Definition get_defs (r:reg) (f:t): list pc :=
  List.concat (
      List.map
        (fun bb =>
           let bid := bb.(fst) in
           let phi_res := List.filter
                        (fun itm => Nat.eqb (itm.(snd).(fst)) r)
                        (BasicBlock.phi_defs bb.(snd)) in
           let phi_idxs := fst (List.split phi_res) in
           let inst_res := List.filter
                        (fun itm => Nat.eqb (itm.(snd).(fst)) r)
                        (BasicBlock.inst_defs bb.(snd)) in
           let inst_idxs := fst (List.split inst_res) in
           (List.map (fun phi_idx => pc_phi bid phi_idx) phi_idxs) ++
           (List.map (fun inst_idx => pc_inst bid inst_idx) inst_idxs))
        (number_list f.(body))).

(* Get PCs of uses of register r. *)
Definition get_uses (r:reg) (f:t): list pc :=
  List.concat (
      List.map
        (fun bb =>
           let bid := bb.(fst) in
           (List.map (fun phi_idx => pc_phi bid phi_idx)
                     (BasicBlock.phi_uses r bb.(snd))) ++
           (List.map (fun inst_idx => pc_inst bid inst_idx)
                     (BasicBlock.inst_uses r bb.(snd))) ++
           (if BasicBlock.terminator_uses r bb.(snd) then
              (pc_inst bid (List.length bb.(snd).(BasicBlock.insts)))::nil
           else nil))
        (number_list f.(body))).

(* Returns true if r is defined in arguments. false otherwise *)
Definition is_argument (r:reg) (f:t): bool :=
  List.existsb (fun x => Nat.eqb x.(snd) r) f.(args).

(* Returns the beginning PC in this function. *)
Definition get_begin_pc (f:t): pc :=
  match f.(body) with
  | nil => (* Cannot happen. in well-formed IR *)
    pc_phi 0 0
  | bb::_ =>
    match bb.(BasicBlock.phis) with
    | phi::_ => pc_phi 0 0
    | nil => pc_inst 0 0
    end
  end.

(* Returns the beginning PC of a basic block which has bbid. *)
Definition get_begin_pc_bb (bbid:nat) (f:t): option pc :=
  match (Ir.IRFunction.getbb bbid f) with
  | Some bb =>
    match (Ir.BasicBlock.phis bb) with
    | nil => Some (Ir.IRFunction.pc_inst bbid 0)
    | _ => Some (Ir.IRFunction.pc_phi bbid 0)
    end
  | None => None
  end.

(* Returns the next pc, if current pc is trivial.
 'Trivial' means: the pc is not pointing to a terminator. *)
Definition next_trivial_pc (p:pc) (f:t): option pc :=
  match p with
  | pc_phi bbid pidx =>
    match (getbb bbid f) with
    | None => None
    | Some bb =>
      if Nat.leb (List.length bb.(BasicBlock.phis)) (1 + pidx) then
        Some (pc_inst bbid 0)
      else
        Some (pc_phi bbid (1 + pidx))
    end
  | pc_inst bbid iidx =>
    match (getbb bbid f) with
    | None => None
    | Some bb =>
      if Nat.ltb iidx (List.length bb.(BasicBlock.insts)) then
        Some (pc_inst bbid (1 + iidx))
      else
        None
    end
  end.

(* Returns phi pc is pointing to.
   If there's no such instruction, returns None. *)
Definition get_phi (p:pc) (f:t): option PhiNode.t :=
  match p with
  | pc_phi bbid pidx =>
    match (getbb bbid f) with
    | None => None
    | Some bb =>
      if Nat.ltb pidx (List.length bb.(BasicBlock.phis)) then
        Some (List.nth pidx bb.(BasicBlock.phis) (0, Ir.ity 0, nil))
      else (* unreachable *)
        None
    end
  | _ => None
  end.

(* Returns the instruction pc is pointing to.
   If there's no such instruction, returns None. *)
Definition get_inst (p:pc) (f:t): option Inst.t :=
  match p with
  | pc_inst bbid iidx =>
    match (getbb bbid f) with
    | None => None
    | Some bb =>
      if Nat.ltb iidx (List.length bb.(BasicBlock.insts)) then
        Some (List.nth iidx bb.(BasicBlock.insts) (Ir.Inst.ievent (Ir.opreg 0)))
      else (* unreachable *)
        None
    end
  | _ => None
  end.

(* Returns the terminator pc is pointing to.
   If there's no such terminator, returns None. *)
Definition get_terminator (p:pc) (f:t): option Terminator.t :=
  match p with
  | pc_inst bbid iidx =>
    match (getbb bbid f) with
    | None => None
    | Some bb =>
      if Nat.eqb iidx (List.length bb.(BasicBlock.insts) +
                       List.length bb.(BasicBlock.phis)) then
        Some (BasicBlock.term bb)
      else (* unreachable *)
        None
    end
  | _ => None
  end.

(* Returns true if the pc is valid. *)
Definition valid_pc (p:pc) (f:t): bool :=
  match p with
  | pc_phi bbid pidx =>
    match (getbb bbid f) with
    | None => false | Some bb => Nat.ltb pidx (List.length bb.(BasicBlock.phis))
    end
  | pc_inst bbid iidx =>
    match (getbb bbid f) with
    | None => false | Some bb => Nat.leb iidx (List.length bb.(BasicBlock.insts))
    end
  end.

Definition valid_next_pc (p1 p2:pc) (f:t): bool :=
  valid_pc p1 f && valid_pc p2 f &&
  match (p1, p2) with
  | (pc_phi bid1 pidx1, pc_phi bid2 pidx2) =>
    Nat.eqb bid1 bid2 && Nat.eqb (pidx1 + 1) pidx2
  | (pc_phi bid1 pidx, pc_inst bid2 iidx) =>
    Nat.eqb bid1 bid2 && Nat.eqb iidx 0 &&
    match (getbb bid1 f) with
    | None => false
    | Some bb => Nat.eqb pidx (List.length bb.(BasicBlock.phis) - 1)
    end
  | (pc_inst bid1 iidx1, pc_inst bid2 iidx2) =>
    Nat.eqb bid1 bid2 && Nat.eqb (iidx1 + 1) iidx2
  | (pc_inst bid1 iidx, pc_phi bid2 pidx) =>
    match (getbb bid1 f, getbb bid2 f) with
    | (Some bb1, Some bb2) =>
      Nat.eqb (List.length bb1.(BasicBlock.insts)) iidx &&
      Terminator.has_dest bid2 (bb1.(BasicBlock.term)) &&
      BasicBlock.valid_phi_idx pidx bb2 &&
      Nat.eqb pidx 0
    | (_, _) => false
    end
  end.

(* Lemmas about PC. *)

Theorem next_trivial_pc_valid:
  forall pc1 pc2 (f:t)
         (HVALID:valid_pc pc1 f = true)
         (HNEXT:next_trivial_pc pc1 f = Some pc2),
    valid_pc pc2 f = true.
Proof.
  intros.
  destruct pc1.
  - (* phi *)
    simpl in HVALID. simpl in HNEXT.
    remember (getbb bbid f) as obb.
    destruct obb as [bb | ].
    + remember (List.length (BasicBlock.phis bb)) as n_phis.
      remember (List.length (BasicBlock.insts bb)) as n_insts.
      destruct n_phis.
      * (* # of phis is 0. *)
        destruct pidx; unfold Nat.ltb in HVALID; simpl in HVALID; inversion HVALID.
      * simpl in HNEXT.
        remember (Nat.leb n_phis pidx) as phi_end.
        destruct phi_end.
        { destruct n_insts.
          - inversion HNEXT.
            simpl. rewrite <- Heqobb. reflexivity.
          - inversion HNEXT.
            simpl. rewrite <- Heqobb. reflexivity.
        }
        { inversion HNEXT.
          simpl. rewrite <- Heqobb. rewrite <- Heqn_phis.
          symmetry in Heqphi_end.
          rewrite Nat.leb_nle in Heqphi_end.
          rewrite Nat.ltb_lt. omega.
        }
    + inversion HNEXT.
  - (* inst *)
    simpl in HVALID. simpl in HNEXT.
    remember (getbb bbid f) as obb.
    destruct obb as [bb | ]; try (inversion HVALID; fail).
    rewrite Nat.leb_le in HVALID.
    remember (List.length (BasicBlock.insts bb)) as n_insts.
    destruct n_insts.
    + inversion HVALID. rewrite H in HNEXT. simpl in HNEXT.
      inversion HNEXT.
    + des_ifs.
      inversion HVALID.
      rewrite H in Heq.
      rewrite Nat.ltb_irrefl in Heq. inv Heq.
      unfold valid_pc. rewrite <- Heqobb. rewrite <- Heqn_insts.
      rewrite Nat.leb_le in *. omega.
Qed.

Theorem get_begin_pc_bb_valid:
  forall bb pc0 fdef
         (HPC:Ir.IRFunction.get_begin_pc_bb bb fdef = Some pc0),
    Ir.IRFunction.valid_pc pc0 fdef.
Proof.
  intros.
  unfold Ir.IRFunction.get_begin_pc_bb in HPC.
  unfold Ir.IRFunction.valid_pc.
  des_ifs.
  rewrite Heq1. simpl. reflexivity.
Qed.


End IRFunction.



Module IRModule.

Definition t := list (IRFunction.t).

Structure wf (mdef:t) := mk_wf
  {
    wf_nonempty: List.length mdef > 0;
    wf_all: forall fdef (HIN:List.In fdef mdef), Ir.IRFunction.wf fdef
  }.

Definition getf (fname2:nat) (m:t): option IRFunction.t :=
    match List.filter (fun f => Nat.eqb fname2 f.(IRFunction.name)) m with
    | nil => None
    | h::t => Some h
    end.

End IRModule.

End Ir.
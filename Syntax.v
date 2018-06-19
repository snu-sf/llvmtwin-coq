Require Import List.
Require Import BinPos.
Require Import Common.

Module Ir.

Inductive ty :=
| ity: nat -> ty (* bitsz *)
| ptrty: ty -> ty.

Inductive const :=
| cnum: ty -> N -> const
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


Module PhiNode.

Definition t:Type := reg * ty * list op.

Definition regops (p:t) :=
  List.concat (List.map regop p.(snd)).

Definition def (p:t):reg * ty :=
  p.(fst).

End PhiNode.


Module Inst.

Inductive t :=
| iadd: reg -> ty -> op -> op -> t (* lhs, retty, op1, op2 *)
| isub: reg -> ty -> op -> op -> t
| ipsub: reg -> ty -> ty -> op -> op -> t (* lhs, retty, ptrty, ptr1, ptr2 *)
| igep: reg -> ty -> op -> op -> bool -> t (* lhs, retty, ptr, idx, inbounds *)
                                           (* For simplicity, retty equals operand ty *)
| iload: reg -> ty -> op -> t (* retty, retty, ptr *)
| istore: ty -> op -> op -> t (* valty, val, ptr *)
| imalloc: reg -> ty -> op -> t (* block size *)
| ifree: op -> t (* pointer *)
| iptrtoint: reg -> op -> ty -> t (* lhs, ptr, retty *)
| iinttoptr: reg -> op -> ty -> t (* rhs, int, retty *)
| ievent: op -> t
| iicmp_ptreq: reg -> ty -> op -> op -> t (* lhs, opty, ptr1, ptr2 *)
| iicmp_ptrule: reg -> ty -> op -> op -> t (* lhs, ptr1, ptr2 *)
.

Definition regops (i:t) :=
  match i with
  | iadd _ _ op1 op2 => (regop op1) ++ (regop op2)
  | isub _ _ op1 op2 => (regop op1) ++ (regop op2)
  | ipsub _ _ _ op1 op2 => (regop op1) ++ (regop op2)
  | igep _ _ op1 op2 _ => (regop op1) ++ (regop op2)
  | iload _ _ op1 => regop op1
  | istore _ op1 op2 => (regop op1) ++ (regop op2)
  | imalloc _ _ op1 => regop op1
  | ifree op1 => regop op1
  | iptrtoint _ op1 _ => regop op1
  | iinttoptr _ op1 _ => regop op1
  | ievent op1 => regop op1
  | iicmp_ptreq _ _ op1 op2 => (regop op1) ++ (regop op2)
  | iicmp_ptrule _ _ op1 op2 => (regop op1) ++ (regop op2)
  end.

Definition def (i:t): option (reg * ty) :=
  match i with
  | iadd r t _ _ => Some (r, t)
  | isub r t _ _ => Some (r, t)
  | ipsub r t _ _ _ => Some (r, t)
  | igep r t _ _ _ => Some (r, t)
  | iload r t _ => Some (r, t)
  | istore _ _ _ => None
  | imalloc r t _ => Some (r, t)
  | ifree _ => None
  | iptrtoint r _ t => Some (r, t)
  | iinttoptr r _ t => Some (r, t)
  | ievent _ => None
  | iicmp_ptreq r _ _ _ => Some (r, ity 1)
  | iicmp_ptrule r _ _ _ => Some (r, ity 1)
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

Definition phi_defs (bb:t): list (nat * (reg * ty)) :=
  List.map (fun pn => (pn.(fst), PhiNode.def pn.(snd)))
           (number_list bb.(phis)).

Definition inst_defs (bb:t): list (nat * (reg * ty)) :=
  List.concat (
    List.map (fun i =>
                match (Inst.def i.(snd)) with
                | Some rt => (i.(fst), rt)::nil | None => nil
             end)
             (number_list bb.(insts))).

End BasicBlock.

Module IRFunction.

Structure t := mkFun
    {retty:ty;
     name:nat;
     args:list (ty * nat);
     body:list BasicBlock.t}.

Definition getbb (bname:nat) (f:t): option BasicBlock.t :=
    match List.filter (fun b => Nat.eqb bname b.(BasicBlock.name)) f.(body) with
    | nil => None
    | h::t => Some h
    end.


(* program counter *)
Inductive pc:Type :=
| pc_phi (bid:nat) (pidx:nat)
| pc_inst (bid:nat) (iidx:nat)
| pc_terminator (bid:nat).


(* Get PCs of definitions of the register.
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

Definition valid_pc (p:pc) (f:t): bool :=
  match p with
  | pc_phi bid pidx =>
    match (getbb bid f) with
    | None => false | Some bb => Nat.ltb pidx (List.length bb.(BasicBlock.phis))
    end
  | pc_inst bid iidx =>
    match (getbb bid f) with
    | None => false | Some bb => Nat.ltb iidx (List.length bb.(BasicBlock.insts))
    end
  | pc_terminator bid =>
    match (getbb bid f) with
    | None => false | Some _ => true
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
    | Some bb => Nat.eqb pidx (List.length bb.(BasicBlock.phis) - 1) &&
                 BasicBlock.valid_inst_idx iidx bb
    end
  | (pc_phi bid1 pidx, pc_terminator bid2) =>
    Nat.eqb bid1 bid2 &&
    match (getbb bid1 f) with
    | None => false
    | Some bb => BasicBlock.valid_phi_idx pidx bb &&
                 Nat.eqb 0 (List.length bb.(BasicBlock.insts))
    end
  | (pc_inst bid1 iidx1, pc_inst bid2 iidx2) =>
    Nat.eqb bid1 bid2 && Nat.eqb (iidx1 + 1) iidx2
  | (pc_inst bid1 iidx1, pc_terminator bid2) =>
    Nat.eqb bid1 bid2 &&
    match (getbb bid1 f) with
    | None => false
    | Some bb => Nat.eqb iidx1 (List.length bb.(BasicBlock.insts) - 1)
    end
  | (pc_terminator bid1, pc_phi bid2 pidx) =>
    match (getbb bid1 f, getbb bid2 f) with
    | (Some bb1, Some bb2) =>
      Terminator.has_dest bid2 (bb1.(BasicBlock.term)) &&
      BasicBlock.valid_phi_idx pidx bb2 &&
      Nat.eqb pidx 0
    | (_, _) => false
    end
  | (pc_terminator bid1, pc_inst bid2 iidx) =>
    Nat.eqb iidx 0 &&
    match (getbb bid1 f, getbb bid2 f) with
    | (Some bb1, Some bb2) =>
      Terminator.has_dest bid2 (bb1.(BasicBlock.term)) &&
      Nat.eqb 0 (List.length bb2.(BasicBlock.phis))
    | (_, _) => false
    end
  | (_, _) => false
  end.

End IRFunction.


Module IRModule.

Definition t := list (IRFunction.t).

Definition getf (fname2:nat) (m:t): option IRFunction.t :=
    match List.filter (fun f => Nat.eqb fname2 f.(IRFunction.name)) m with
    | nil => None
    | h::t => Some h
    end.

End IRModule.

End Ir.
Require Import List.
Require Import Nat.

Module Ir.

Inductive ty :=
| ity: nat -> ty (* bitsz *)
| ptrty: ty -> ty.

Inductive const :=
| cnum: ty -> nat -> const
| cnullptr: ty -> const
| cpoison: ty -> const
| cglb: nat -> const
| cvec: list const -> const.

Definition reg := nat.

Inductive op :=
| opconst: const -> op
| opreg: reg -> op.

Inductive inst :=
| iadd: reg -> ty -> op -> op -> inst (* lhs, retty, op1, op2 *)
| isub: reg -> ty -> op -> op -> inst
| ipsub: reg -> ty -> op -> op -> inst (* lhs, retty, ptr1, ptr2 *)
| igep: reg -> ty -> op -> op -> bool -> inst (* lhs, retty, ptr, idx, inbounds *)
| iload: reg -> ty -> op -> nat -> inst (* retty, ptr, access-size *)
| istore: ty -> op -> op -> nat -> inst (* valty, val, ptr, access-size *)
| imalloc: nat -> inst (* block size *)
| ifree: op -> inst (* pointer *)
| iptrtoint: reg -> op -> ty -> inst (* lhs, ptr, retty *)
| iinttoptr: reg -> op -> ty -> inst (* rhs, int, retty *)
| ievent: op -> inst
| iicmp_ptreq: reg -> op -> op -> inst (* lhs, ptr1, ptr2 *)
| iicmp_ptrule: reg -> op -> op -> inst (* lhs, ptr1, ptr2 *)
.

Inductive terminator :=
| tbr: terminator (* unconditional branch *)
| tbr_cond: op -> nat -> nat -> terminator
| tret: op -> terminator (* returning value, instruction *)
.

Structure basicblock := mkBB
    {bbname:nat; bbinsts:list inst; bbterm:terminator}.

Structure function := mkFun
    {fretty:ty; fname:nat;
     fargs:list (ty * nat);
     fbody:list basicblock}.

Definition getbb (f:function) (bname:nat): option basicblock :=
    match List.filter (fun b => Nat.eqb bname b.(bbname)) f.(fbody) with
    | nil => None
    | h::t => Some h
    end.

Definition module := list function.

Definition getf (m:module) (fname2:nat): option function :=
    match List.filter (fun f => Nat.eqb fname2 f.(fname)) m with
    | nil => None
    | h::t => Some h
    end.

End Ir.
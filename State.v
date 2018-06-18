Require Import Common.
Require Import Syntax.
Require Import Memory.
Require Import BinPos.
Require Import List.

Module Ir.

Inductive val :=
| num: N -> val | ptr: Ir.ptrval -> val
| poison: val.

Definition regfile := list (nat * val).
Definition stack := list Ir.callid.
Definition pc := prod nat nat. (* block id, inst pos *)

Module Config.

Structure t := mk
  {
    r:regfile; m:Ir.Memory.t; s:stack; p:pc;
    cid_to_f:list (Ir.callid * nat); (*callid -> function id*)
    cid_fresh: Ir.callid
  }.

Definition get_rval (c:t) (regid:nat): option val :=
  match (List.filter (fun x => Nat.eqb x.(fst) regid) c.(r)) with
  | nil => None
  | h::t => Some h.(snd)
  end.

Definition get_val (c:t) (o:Ir.op): option val:=
  match o with
  | Ir.opconst c => Some
    match c with
    | Ir.cnum cty cn => num cn
    | Ir.cnullptr cty => ptr Ir.NULL
    | Ir.cpoison cty => poison
    | Ir.cglb glbvarid => ptr (Ir.plog (glbvarid, 0))
    end
  | Ir.opreg regid => get_rval c regid
  end.

Definition update_rval (c:t) (regid:nat) (v:val): t :=
  mk ((regid, v)::c.(r)) c.(m) c.(s) c.(p) c.(cid_to_f) c.(cid_fresh).

Definition get_funid (c:t) (cid:Ir.callid): option nat :=
  match (List.filter (fun x => Nat.eqb x.(fst) cid) c.(cid_to_f)) with
  | nil => None
  | h::t => Some h.(snd)
  end.

End Config.

End Ir.
Require Import Common.
Require Import Lang.
Require Import Memory.
Require Import BinPos.
Require Import List.
Require Import Value.

Module Ir.

Definition regfile := list (nat * Ir.val).
Definition stack := list Ir.callid.
Definition pc := prod nat nat. (* block id, inst pos *)
Inductive event :=
| e_none: event
| e_some (v:Ir.val): event.

Module Config.

Structure t := mk
  {
    r:regfile; m:Ir.Memory.t; s:stack; p:pc;
    cid_to_f:list (Ir.callid * nat); (*callid -> function id*)
    cid_fresh: Ir.callid
  }.

Definition get_rval (c:t) (regid:nat): option Ir.val :=
  match (List.filter (fun x => Nat.eqb x.(fst) regid) c.(r)) with
  | nil => None
  | h::t => Some h.(snd)
  end.

Definition get_val (c:t) (o:Ir.op): option Ir.val:=
  match o with
  | Ir.opconst c => Some
    match c with
    | Ir.cnum cty cn => Ir.num cn
    | Ir.cnullptr cty => Ir.ptr Ir.NULL
    | Ir.cpoison cty => Ir.poison
    | Ir.cglb glbvarid => Ir.ptr (Ir.plog (glbvarid, 0))
    end
  | Ir.opreg regid => get_rval c regid
  end.

Definition update_rval (c:t) (regid:nat) (v:Ir.val): t :=
  mk ((regid, v)::c.(r)) c.(m) c.(s) c.(p) c.(cid_to_f) c.(cid_fresh).

Definition update_m (c:t) (m:Ir.Memory.t): t :=
  mk c.(r) m c.(s) c.(p) c.(cid_to_f) c.(cid_fresh).

Definition get_funid (c:t) (cid:Ir.callid): option nat :=
  match (List.filter (fun x => Nat.eqb x.(fst) cid) c.(cid_to_f)) with
  | nil => None
  | h::t => Some h.(snd)
  end.

End Config.

End Ir.
Require Import Common.
Require Import Lang.
Require Import Memory.
Require Import BinPos.
Require Import List.
Require Import Value.

Module Ir.

Definition regfile := list (nat * Ir.val).
Definition stack := list (Ir.callid * Ir.IRFunction.pc).


Module Config.

Structure t := mk
  {
    r:regfile;
    m:Ir.Memory.t;
    s:stack;
    cid_to_f:list (Ir.callid * nat); (*callid -> function id*)
    cid_fresh: Ir.callid;
    md:Ir.IRModule.t
  }.

Structure wf (c:t) := mk_wf
  {
    wf_m: Ir.Memory.wf c.(m);
    wf_cid_to_f: List.NoDup (List.map fst c.(cid_to_f));
    wf_cid_to_f2: forall cf (HIN:List.In cf c.(cid_to_f)),
        exists f, Ir.IRModule.getf cf.(snd) c.(md) = Some f;
    wf_stack: forall curcid curpc funid f (HIN:List.In (curcid, curpc) c.(s))
                     (HIN2:List.In (curcid, funid) c.(cid_to_f))
                     (HF:Some f = Ir.IRModule.getf funid c.(md)),
        Ir.IRFunction.valid_pc curpc f = true
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
  mk ((regid, v)::c.(r)) c.(m) c.(s) c.(cid_to_f) c.(cid_fresh) c.(md).

Definition update_m (c:t) (m:Ir.Memory.t): t :=
  mk c.(r) m c.(s) c.(cid_to_f) c.(cid_fresh) c.(md).

Definition get_funid (c:t) (cid:Ir.callid): option nat :=
  match (list_find_key c.(cid_to_f) cid) with
  | nil => None
  | h::t => Some h.(snd)
  end.

Definition update_pc (c:t) (next_pc:Ir.IRFunction.pc): t :=
  match c.(s) with
  | (cid, pc0)::t => mk c.(r) c.(m) ((cid,next_pc)::t) c.(cid_to_f) c.(cid_fresh) c.(md)
  | _ => c
  end.

Definition cur_fdef_pc (c:t): option (Ir.IRFunction.t * Ir.IRFunction.pc) :=
  match (Ir.Config.s c) with
  | (cid, pc0)::t =>
    match Ir.Config.get_funid c cid with
    | Some funid =>
      match Ir.IRModule.getf funid c.(md) with
      | Some fdef => Some (fdef, pc0)
      | None => None
      end
    | None => None
    end
  | nil => None
  end.

Definition has_nestedcall (c:t): bool :=
  Nat.ltb 1 (List.length (Ir.Config.s c)).

End Config.

End Ir.
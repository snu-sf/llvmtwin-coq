Require Import Common.
Require Import Lang.
Require Import Memory.
Require Import BinPos.
Require Import List.
Require Import Value.

Module Ir.

(* Definition of a register file. *)
Definition regfile := list (nat * Ir.val).
(* Definition of a call stack. *)
Definition stack := list (Ir.callid * (Ir.IRFunction.pc * regfile)).


Module Config.

(* Definition of a program state. *)
Structure t := mk
  {
    m:Ir.Memory.t; (* a memory *)
    s:stack; (* a call stack *)
    cid_to_f:list (Ir.callid * nat); (*callid -> function id*)
    cid_fresh: Ir.callid; (* Fresh, unused call id. *)
    md:Ir.IRModule.t (* IR module *)
  }.

(* Wellformedness of a program state. *)
Structure wf (c:t) := mk_wf
  {
    (* wf_m: Memory is also well-formed. *)
    wf_m: Ir.Memory.wf c.(m);
    (* wf_cid_to_f: there's no duplicated
       call ids in cid_to_f. which is a mapping from
       CallID to Function name (= function id)
       *)
    wf_cid_to_f: List.NoDup (list_keys c.(cid_to_f));
    (* wf_cid_to_f2: All function ids in cid_to_f are valid, i.e.,
       has corresponding function definition. *)
    wf_cid_to_f2: forall cf (HIN:List.In cf c.(cid_to_f)),
        exists f, Ir.IRModule.getf cf.(snd) c.(md) = Some f;
    (* wf_stack: all PCs stored in the call stack (which is c.(s))
       are valid, respective to corresponding functions. *)
    wf_stack: forall curcid curpc funid f curregfile
                     (HIN:List.In (curcid, (curpc, curregfile)) c.(s))
                     (HIN2:List.In (curcid, funid) c.(cid_to_f))
                     (HF:Some f = Ir.IRModule.getf funid c.(md)),
        Ir.IRFunction.valid_pc curpc f = true
    (* WIP - more properties will be added later. *)
  }.

(* Get register value. *)
Definition get_rval (c:t) (regid:nat): option Ir.val :=
  match c.(s) with
  | nil => None
  | (_, (_, r))::_ =>
    match (List.filter (fun x => Nat.eqb x.(fst) regid) r) with
    | nil => None
    | h::t => Some h.(snd)
    end
  end.

(* Get value of the operand o. *)
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

(* Update value of register regid. *)
Definition update_rval (c:t) (regid:nat) (v:Ir.val): t :=
  match c.(s) with
  | nil => c
  | (cid, (pc0, r))::s' =>
    mk c.(m) ((cid, (pc0, (regid, v)::r))::s') c.(cid_to_f) c.(cid_fresh) c.(md)
  end.

(* Update memory. *)
Definition update_m (c:t) (m:Ir.Memory.t): t :=
  mk m c.(s) c.(cid_to_f) c.(cid_fresh) c.(md).

(* Get function id (= function name) of cid. *)
Definition get_funid (c:t) (cid:Ir.callid): option nat :=
  match (list_find_key c.(cid_to_f) cid) with
  | nil => None
  | h::t => Some h.(snd)
  end.

(* Update PC into next_pc. *)
Definition update_pc (c:t) (next_pc:Ir.IRFunction.pc): t :=
  match c.(s) with
  | (cid, (pc0, r))::t => mk c.(m) ((cid,(next_pc, r))::t) c.(cid_to_f) c.(cid_fresh) c.(md)
  | _ => c
  end.

(* Get (definition of the running function, PC inside the function). *)
Definition cur_fdef_pc (c:t): option (Ir.IRFunction.t * Ir.IRFunction.pc) :=
  match (Ir.Config.s c) with
  | (cid, (pc0, _))::t =>
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

(* Returns true if the call stack has more than one entry, false otherwise. *)
Definition has_nestedcall (c:t): bool :=
  Nat.ltb 1 (List.length (Ir.Config.s c)).

End Config.

End Ir.
Require Import BinPos.
Require Import List.
Require Import Omega.

Require Import Common.
Require Import Lang.
Require Import Memory.
Require Import Value.


Module Ir.

Module Regfile.
(* Definition of a register file. *)
Definition t := list (nat * Ir.val).

Definition get (rf:t) (regid:nat): option Ir.val :=
  match (list_find_key rf regid) with
  | nil => None
  | h::t => Some h.(snd)
  end.

Definition update (rf:t) (regid:nat) (v:Ir.val): t :=
  (regid,v)::rf.

(* Definition of two regfiles. *)
Definition eq (r1 r2:t): Prop :=
  forall regid, get r1 regid = get r2 regid.


(***************************************************
              Lemmas about Regfile.
 ***************************************************)

Theorem update_eq:
  forall (r1 r2:t) (HEQ:eq r1 r2)
         (regid:nat) (v:Ir.val),
    eq (update r1 regid v) (update r2 regid v).
Proof.
  unfold eq in *.
  intros.
  unfold update.
  unfold get.
  simpl.
  destruct (regid =? regid0) eqn:Heqid.
  - simpl. reflexivity.
  - unfold get in HEQ.
    rewrite HEQ. reflexivity.
Qed.

Theorem update_reordered_eq:
  forall (rf:t) (rid1 rid2:nat) (v1 v2:Ir.val)
         (HNEQ:Nat.eqb rid1 rid2 = false),
    eq (update (update rf rid1 v1) rid2 v2)
       (update (update rf rid2 v2) rid1 v1).
Proof.
  intros.
  unfold update.
  simpl.
  unfold eq.
  intros.
  unfold get.
  simpl.
  destruct (rid2 =? regid) eqn:Heqid2;
    destruct (rid1 =? regid) eqn:Heqid1;
    try (rewrite Nat.eqb_eq in *);
    try (rewrite Nat.eqb_neq in *).
  - omega.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

End Regfile.


Module Stack.

(* Definition of a call stack. *)
Definition t := list (Ir.callid * (Ir.IRFunction.pc * Regfile.t)).

Definition eq (s1 s2:t):Prop :=
  List.Forall2 (fun itm1 itm2 =>
                  itm1.(fst) = itm2.(fst) /\ itm1.(snd).(fst) = itm2.(snd).(fst) /\
                  Regfile.eq itm1.(snd).(snd) itm2.(snd).(snd))
               s1 s2.

End Stack.


Module Config.

(* Definition of a program state. *)
Structure t := mk
  {
    m:Ir.Memory.t; (* a memory *)
    s:Stack.t; (* a call stack *)
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
  | (_, (_, r))::_ => Regfile.get r regid
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
    mk c.(m) ((cid, (pc0, Regfile.update r regid v))::s') c.(cid_to_f) c.(cid_fresh) c.(md)
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

(* Returns the instruction pc is pointing to. *)
Definition cur_inst (c:t): option (Ir.Inst.t) :=
  match cur_fdef_pc c with
  | Some (fdef, pc0) => Ir.IRFunction.get_inst pc0 fdef
  | None => None
  end.

(* Returns true if the call stack has more than one entry, false otherwise. *)
Definition has_nestedcall (c:t): bool :=
  Nat.ltb 1 (List.length (Ir.Config.s c)).


(* Definition of equality. *)
(*     m:Ir.Memory.t; (* a memory *)
    s:Stack.t; (* a call stack *)
    cid_to_f:list (Ir.callid * nat); (*callid -> function id*)
    cid_fresh: Ir.callid; (* Fresh, unused call id. *)
    md:Ir.IRModule.t (* IR module *)*)
Definition eq (c1 c2:t): Prop :=
  c1.(m) = c2.(m) /\ Stack.eq c1.(s) c2.(s) /\ c1.(cid_to_f) = c2.(cid_to_f) /\
  c1.(cid_fresh) = c2.(cid_fresh) /\ c1.(md) = c2.(md).

End Config.

End Ir.
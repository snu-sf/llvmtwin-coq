### About

This is a Coq formalization of OOPSLA'18 LLVM memory model.

Compile with Coq 8.8.1 please.

### Definition of Memory

- Definition of memory: `Ir.Memory.t` in [Memory.v](Memory.v)
    + `Ir.Memory.t` means `t` in `Module Memory` in `Module Ir`.

- Well-formedness of a memory: `Ir.Memory.wf` in [Memory.v](Memory.v)

- Definition of a memory block: `Ir.MemBlock.t` in [Memory.v](Memory.v)

- Well-formedness of a memory block: `Ir.MemBlock.wf` in [Memory.v](Memory.v)

- Definition of dereferenceability: `Ir.deref` in [LoadStore.v](LoadStore.v)

- Semantics of load/store: `Ir.load_val`/`Ir.store_val` in [LoadStore.v](LoadStore.v)

- Definition of twin state, observedness, guessed pointer, etc: [TwinExecution.v](TwinExecution.v)


### Definition of IR syntax & Program Behavior

- Definition of IR syntax: [Lang.v](Lang.v)
    + Phi node: `Ir.PhiNode.t` (or 't' in `Module PhiNode` in `Module Ir`)
    + Instruction: `Ir.Inst.t`
    + Terminator: `Ir.Terminator.t`
    + Basic block: `Ir.BasicBlock.t`
    + Function: `Ir.IRFunction.t`
    + Module: `Ir.IRModule.t`
    + Note: for simplicity, function call and return instruction is not included in our language.

- Definition of small-step semantics of IR instructions: [SmallStep.v](SmallStep.v)

- Definition of a program state: `Ir.Config.t` in [State.v](State.v)

- Well-formedness of a program state: `Ir.Config.wf` in [State.v](State.v)

- Definition of an event: `event` in [Behaviors.v](Behaviors.v)

- Definition of a program behavior: `Ir.program_behavior` in [Behaviors.v](Behaviors.v)

- Definition of refinement : `Ir.refines` in [Refinement.v](Refinement.v)
    - It is showed that refinement is reflexive as well as transitive.


### Proofs

- Small-step of instructions preserve wellformedness of state: [SmallStepWf.v](SmallStepWf.v)
    - Theorem `sstep_wf` shows that if input state is well-formed, and executing small step on the state successesfully made output state, the output state is also well-formed.

- Proof of a property of a guessed address (sec. 4.11): [TwinExecutionProof.v](TwinExecutionProof.v)
    - Theorem `malloc_creates_twin_state` states that malloc either returns a NULL pointer, or it creates a twin state.
    - Theorem `twin_execution` states that 'twin-state-ness' is preserved if the block is not observed and no memory access through a guessed pointer is made.
    - Theorem `access_from_guessed_pointer_fails` states that if a guessed pointer accesses a block at state st1, then the access fails at twin state st2.

- Reordering of interested instructions: [Reordering.v](Reordering.v) 
    - This proves that ptrtoint/inttoptr/getelementptr/icmp eq/icmp ule/psub can be freely reordered with respect to malloc/free.
    
- Correctness of GVN on pointer equality (sec. 5): [GVN1.v](GVN1.v), [GVN2.v](GVN2.v), [GVN3.v](GVN3.v), [GVN4.v](GVN4.v)
    - [GVN1.v](GVN1.v) proves that replacing p with q is valid if q is NULL or the result of an integer-to-pointer cast.
        - It defines a notion of `physicalized_ptr p q`, meaning that either (informally) `q = (int*)(uintptr_t)p` holds, or `p = gep [inbounds] p0` and `q = gep [inbounds] q0` that satisfies `physicalized_ptr p0 q0`.
        - Theorem `physicalized_ptr_spec` shows that if `icmp eq p, q` evaluates to true, and q is a vanilla physical pointer,  then `physicalized_ptr p q` holds.
        - Theorems `*_refines` show that for all operations that take pointer as operand, refinement holds if `p` is replaced with `q`.
    - [GVN2.v](GVN2.v) proves that replacing p with q is valid if p and q are logical pointers, and both are either dereferenceable or they point to the same block.
        - It shows that if p and q satisfies the condition, and `icmp eq p, q` evaluates to true, p and q have same value.
    - [GVN3.v](GVN3.v) proves that replacing p with q is valid if p and q are both computed by the gep inbounds with same base pointer.
        - It shows that if p and q satisfies the condition, and `icmp eq p, q` evaluates to true, p and q have same value.
    - [GVN4.v](GVN4.v) proves that replacing p with q is valid if either p or q is computed by a series of gep inbounds with positive offsets, based on the same base pointer.
        - It defines a notion of `gepinbs p q p0`, meaning that p and q are series of gep inbounds with positive offsets, based on p0.
        - Theorem `gepinbs_after_icmpeq_true` shows that, if `icmp eq p q` evaluates to true, and `gepinbs p q p0` holds for any pointer p0, either p and q are equal or `phys_minmaxI p1 p2` holds. `phys_minmaxI p1 p2` means that p1 and p2 are physical pointers with `p1.I` and `p2.I` having same min/max value.
        - Later on, GVN4.v shows that if `phys_minmaxI p1 p2` holds, then replacing p1 with p2 is valid (refinement holds) for all instructions which take pointer as operand. 

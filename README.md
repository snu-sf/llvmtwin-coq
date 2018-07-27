### About

This is a Coq formalization of OOPSLA'18 LLVM memory model.


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

- Definition of small-step semantics of IR instructions: [SmallStep.v](SmallStep.v)

- Definition of a program state: `Ir.Config.t` in [State.v](State.v)

- Well-formedness of a program state: `Ir.Config.wf` in [State.v](State.v)

- Definition of an event: `event` in [Behaviors.v](Behaviors.v)

- Definition of a program behavior: `Ir.program_behavior` in [Behaviors.v](Behaviors.v)

- Definition of refinement : `Ir.refines` in [Refinement.v](Refinement.v)
    - It is showed that refinement is reflexive as well as transitive.


### Proofs

- Proof of a property of a guessed address (sec. 4.11): [TwinExecutionProof.v](TwinExecutionProof.v)
    - Theorem `malloc_creates_twin_state` states that malloc either returns a NULL pointer, or it creates a twin state.
    - Theorem `twin_execution` states that 'twin-state-ness' is preserved if the block is not observed.
    - Theorem `access_from_guessed_pointer_fails` states that if a guessed pointer accesses a block, then the access fails at the twin state.

- Reordering of interested instructions: [Reordering.v](Reordering.v) 
    - This proves that ptrtoint/inttoptr/getelementptr/icmp eq/icmp ule/psub can be freely reordered with respect to malloc/free.
    
- Correctness of GVN on pointer equality (sec. 5): [GVN1.v](GVN1.v), [GVN2.v](GVN2.v)
    - [GVN1.v](GVN1.v): Proves that replacing p with q is valid if q is NULL or the result of an integer-to-pointer cast.
        - It defines a notion of `physicalized_ptr p q`, meaning that either (informally) `q = (int*)(uintptr_t)p` holds, or `p = gep [inbounds] p0` and `q = gep [inbounds] q0` that satisfies `physicalized_ptr p0 q0`.
        - Theorem `physicalized_ptr_spec` shows that if `icmp eq p, q` evaluates to true, and q is a vanilla physical pointer,  then `physicalized_ptr p q` holds.
        - Theorems `*_refines` show that for all operations that take pointer as operand, refinement holds if `p` is replaced with `q`.
    - [GVN2.v](GVN2.v): Proves that replacing p with q is valid if p and q are logical pointers, and both are either dereferenceable or they point to the same block.
        - It shows that if p and q satisfies the condition, and `icmp eq p, q` evaluates to true, p and q have same value.

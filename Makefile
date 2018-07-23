all:
	coqc sflib.v
	coqc Common.v
	coqc Memory.v
	coqc Value.v
	coqc Lang.v
	coqc LoadStore.v
	coqc State.v
	coqc Behaviors.v
	coqc WellTyped.v
	coqc SmallStep.v SmallStepTest.v
	coqc Refinement.v
	coqc Reordering.v TwinExecution.v
	coqc TwinExecutionProof.v
	coqc GVN.v

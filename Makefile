all:
	coqc sflib.v
	coqc Common.v
	coqc Memory.v
	coqc Lang.v
	coqc LoadStore.v State.v WellTyped.v

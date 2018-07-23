Require Import BinPos.
Require Import Memory.

Module Ir.

Inductive val :=
| num: nat -> val
| ptr: Ir.ptrval -> val
| poison: val.

End Ir.
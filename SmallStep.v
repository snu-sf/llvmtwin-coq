Require Import Common.
Require Import Memory.
Require Import Syntax.
Require Import State.
Require Import BinNatDef.

Module Ir.

Definition sstep_det (c:Ir.Config.t) (i:Ir.inst): option Ir.Config.t :=
  match i with
  | Ir.iadd r (Ir.ity bsz) op1 op2 =>
    Ir.Config.update_rval c r
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      | (Some (Ir.num i1), Some (Ir.num i2)) =>
        Ir.num (N.modulo (N.add i1 i2) (N.shiftl 2%N (N.of_nat bsz)))
      | (_, _) => Ir.poison
      end
  | Ir.isub r (Ir.ity bsz) op1 op2 =>
    Ir.Config.update_rval c r
      match (Ir.Config.get_val c op1, Ir.Config.get_val c op2) with
      | (Some (Ir.num i1), Some (Ir.num i2)) =>
        Ir.num (N.modulo (N.sub (N.add i1 (N.shiftl 2%N (N.of_nat bsz))) i2)
                                (N.shiftl 2%N (N.of_nat bsz)))
      | (_, _) => Ir.poison
      end
  | Ir.ipsub r (Ir.ity bsz) (Ir.ptrty opty) op1 op2 =>
    c
  | Ir.igep r (Ir.ptrty retty) opptr opidx inb =>
    c
  | Ir.iload r retty opptr =>
    c
  | Ir.istore r valty opptr opval =>
    c
  | Ir.imalloc r blocksz =>
    (* malloc is not determinstic! *)
    None
  | Ir.ifree opptr =>
    c
  | Ir.iptrtoint r opptr (Ir.ity retty) =>
    c
  | Ir.iinttoptr r opint (Ir.ptrty retty) =>
    c
  | Ir.ievent opval =>
    c
  | Ir.iicmp_ptreq r opty opptr1 opptr2 =>
    c
  | Ir.iccmp_ptrule r opty opptr1 opttr2 =>
    c
  | _ => None (* Untyped IR *)
  end.

End Ir.
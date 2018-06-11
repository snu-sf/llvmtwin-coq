
namespace ir

inductive ty
| ity : ℕ → ty -- bitsz
| ivecty : ℕ → ℕ → ty -- # of elem, bitsz
| ptrty : ty → ty
| pvecty : ℕ → ty → ty -- # of elem, elem ty

inductive const
| num: ty → ℕ → const
| nullptr: ty → const
| poison: ty → const
| glb: string → const
| vec: list const → const

def reg := string

inductive op
| const: const → op
| reg: reg → op

inductive inst
| add: reg → ty → op → op → inst -- lhs, retty, op1, op2
| sub: reg → ty → op → op → inst
| psub: reg → ty → op → op → inst -- lhs, retty, ptr1, ptr2
| gep: reg → ty → op → op → bool → inst -- lhs, retty, ptr, idx, inbounds
| load: reg → ty → op → nat → inst -- retty, ptr, access-size
| store: ty → op → op → nat → inst -- valty, val, ptr, access-size
| malloc: nat → inst -- block size
| free: op → inst -- pointer
| call: reg → ty → reg → list op → inst -- lhs, retty, funcname, args
| ptrtoint: reg → op → ty → inst -- lhs, ptr, retty
| inttoptr: reg → op → ty → inst -- rhs, int, retty
| event: op → inst
| icmp_ptreq: reg → op → op → inst -- lhs, ptr1, ptr2
| icmp_ptrule: reg → op → op → inst -- lhs, ptr1, ptr2

inductive terminator
| br: string → terminator -- unconditional branch
| br_cond: op → string → string → terminator
| ret: op → terminator -- returning value, instruction

structure basicblock :=
    (name:string) (insts:(list inst)) (term:terminator)


structure function := 
    (retty:ty) (name:string)
    (args:list (ty × string))
    (body:list basicblock)

namespace function
def get (f:function) (bname:string): option basicblock :=
    match f.body.filter (λ f:basicblock, f.name = bname) with
    | [] := none
    | h::t := some h
    end
end function


def module := list function

namespace module
def get (m:module) (fname:string): option function :=
    match m.filter (λ f:function, f.2 = fname) with
    | [] := none
    | h::t := some h
    end
end module

end ir
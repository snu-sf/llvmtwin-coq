import .common

namespace ir

def PTRSZ := 16
def MEMSZ := nat.pow 2 PTRSZ
def TWINCNT := 3

@[reducible]
def blockid := nat
@[reducible]
def callid := nat
@[reducible]
def time := nat

inductive ptrval
-- Log(l, o) where 0 <= o < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
| log: blockid × nat → ptrval
-- Phy(o, I, cid) where 0 <= o, i(∈ I) < MEMSZ
-- Note that 0 <= o < MEMSZ is kept as invariant of memory.
-- Note: no address space
| phy: nat × list nat × callid → ptrval 

inductive blockty
| stack | heap | global | function

inductive bit
| b:bool → bit
-- (p, i)
-- Note that 0 ≤ i < 64 is kept as invariant.
| addrb: ptrval → nat → bit

structure byte :=
    (b0 b1 b2 b3 b4 b5 b6 b7:bit)

-- Block := (t, r, n, a, c, P)
-- Note that |P| == twin# is kept as invariant.
structure memblock :=
    (t:blockty) (r:time × option time)
    (n:nat) (a:nat) (c:list byte)
    (P:list nat)

namespace memblock

@[reducible]
def P_size (mb:memblock) := mb.P.map (λ b, (b, mb.n))

-- Well-formedness of a memory block.
structure wf (mb:memblock) :=
    (tcond: ∀ t (FREED:mb.r.2 = some t), mb.r.1 < t)
    (clen: mb.c.length = mb.n)
    (align: ∀ p (HAS:p ∈ mb.P), nat.mod p mb.a = 0)
    (inmem: ∀ p (HAS:p ∈ mb.P), p + mb.n < MEMSZ)
    (notnull: ∀ p (HAS:p ∈ mb.P), p ≠ 0)
    (disj: disjoint mb.P_size)
    (twin: mb.P.length = TWINCNT)

@[reducible]
def alive (mb:memblock) := mb.r.2 = none

end memblock


structure memory := 
    (t:time) (blocks:list (blockid × memblock)) (calltimes:list (callid × option time))

namespace memory

-- Well-formedness of memory.
structure wf (m:memory) :=
    (blocks: ∀ i p (HAS:(i, p) ∈ m.blocks), memblock.wf p)
    (uniqueid: list.unique (m.blocks.map (λi, i.1)))
    (uniquecid: list.unique (m.calltimes.map (λi, i.1)))

def alive_blocks (m:memory): list (blockid × memblock) :=
    m.blocks.filter (λ a, a.2.alive)

-- Checks whether newmb's P does not overlap with other blocks.
def allocatable (m:memory) (newmb:memblock) := 
    ∀ i (b:memblock) (HAS:(i,b) ∈ m.blocks), disjoint (newmb.P_size++(b.P_size))

def get (m:memory) (i:blockid): option memblock :=
    match (m.blocks.filter (λ (itm:blockid × memblock), itm.1 = i)) with
    | a::b := some a.2
    | nil := none
    end

end memory

end ir
universe u

-- disjoint L n1 beg2 n2:
-- Forall (beg_i, n_i) ∈ L, is (beg_i, beg_i + n_i) disjoint with each other?
inductive disjoint: list (nat × nat) → Prop
| nil: disjoint []
| cons: ∀ (beg2 n2:nat) (l:list (nat × nat))
    (H:disjoint l)
    (H2:∀ beg_i n_i (HIN:(beg_i, n_i) ∈ l),
          beg_i + n_i < beg2 ∨ beg2 + n2 < beg_i),
    disjoint ((beg2, n2)::l)

inductive list.unique {α:Type u}: list α → Prop
| nil: list.unique []
| cons: ∀ a l (H:list.unique l) (H2:a ∉ l), list.unique (a::l)

import .common
import .syntax

namespace ir

namespace function

structure wf (f:function) :=
    (bbone:f.body ≠ [])
    (bbnames:list.unique (f.body.map (λ (k:basicblock), k.name)))
    (bbterms:∀ (b:basicblock) (HAS:b ∈ f.body),
            ∃ b', f.get b.name = some b' ∧ b' ∈ f.body)

end function


namespace module

structure wf (m:module) :=
    (fnames: list.unique (m.map (λ (f:function), f.name)))

end module

end ir
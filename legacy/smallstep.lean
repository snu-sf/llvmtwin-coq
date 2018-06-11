import .syntax
import .state
import .event

namespace ir

inductive istep: config → inst → (config × option event) → Prop
| add: ∀ i r rty op1 op2,
    i = inst.add r rty op1 op2 →

end ir
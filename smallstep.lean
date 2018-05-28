import .syntax
import .state

namespace ir

inductive sstep: config → program → (config × option event) → Prop

end ir
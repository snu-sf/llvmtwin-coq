import .syntax
import .memory

namespace ir

inductive val
| num: nat → val
| ptr: ptrval → val

def regfile := list (string × val)
def pc := string × nat -- block name, inst #
def stack := list callid -- list of call id

def config := regfile × memory × stack × pc

end ir
import .syntax
import .memory

namespace ir

inductive val
| num: nat → val
| ptr: ptrval → val

def regfile := list (string × val)
def pc := string × nat -- block name, inst #
def stack := list callid -- list of call id

structure config :=
    (r:regfile) (m:memory) (s:stack) (p:pc)
    (cidtofname:list (callid × string))
    (freshcid:callid)

namespace config

-- regfile

def getval (c:config) (name:string): option val :=
    match c.r.filter (λ (x:string × val), x.1 = name) with
    | [] := none
    | h::t := some h.2
    end

def updateval (c:config) (name:string) (v:val): config :=
    {c with r := (name, v)::c.r}

def getfuncname (c:config) (cid:callid): option string :=
    match c.cidtofname.filter (λ (t:callid × string), t.1 = cid) with
    | [] := none
    | h::t := some h.2
    end

end config

end ir
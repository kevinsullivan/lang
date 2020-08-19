import ...phys.src.classical_time

namespace lang.classicalTime

structure var : Type :=
mk :: (num : ℕ) 

def varEq : var → var → bool
| v1 v2 := v1.num=v2.num

def env := (var → classicalTime)

inductive expr
| lit (v : classicalTime) 
| var (v : var)

def eval : expr → env → classicalTime
| (expr.lit V) E := V
| (expr.var v) E := E v

def override : env → var → expr → env   -- clone
| i v e := λ r,     if (varEq v r) 
                    then (eval e i) 
                    else (i r)

def init := λ v : var, worldTime

end lang.classicalTime
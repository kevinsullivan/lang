import ...phys.src.classical_velocity
import .classical_geometry
import .classical_time

namespace lang.classicalVelocity

structure var : Type :=
mk :: (num : ℕ)

def varEq : var → var → bool
| v1 v2 := v1.num=v2.num

def env := (var → classicalVelocity)

inductive expr : Type
| lit (v : classicalVelocity)
| var (v : var)
| div (g : lang.classicalGeometry.expr) (t : lang.classicalTime.expr)

def eval : expr → env → classicalVelocity 
| (expr.lit v) i := v
| (expr.var v) i := i v
| (expr.div g t) i := _ -- TODO: WHAT GOES HERE?

def override : env → var → expr → env
| i v e := λ r,     if (varEq v r) 
                    then (eval e i) 
                    else (i r)

def init := λ v : var, worldVelocity

end lang.classicalVelocity
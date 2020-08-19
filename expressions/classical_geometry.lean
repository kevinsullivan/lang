import ...phys.src.classical_geometry

namespace lang.classicalGeometry

structure var : Type := 
mk :: (num : ℕ) 

def varEq : var → var → bool
| v1 v2 := v1.num = v2.num -- implicit coercion here

inductive expr
| lit (s : classicalGeometry) : expr
| var (v : var) : expr
--| GeometricProduct (e1 e2 : classicalGeometryexpr) : classicalGeometryexpr

def env := (var → classicalGeometry)

def eval : expr → env → classicalGeometry 
| (expr.lit s) e := s
| (expr.var v) e := e v
--| (classicalGeometryexpr.GeometricProduct V1 V2) E := V1 --not sure how to combine spaces yet

def override : env → var → expr → env
| i v e := λ r,   if (varEq v r) 
                    then (eval e i) 
                    else (i r)

def init := λ v : var, worldGeometry

end lang.classicalGeometry
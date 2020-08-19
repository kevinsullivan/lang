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

def init := λ v : var, worldGeometry

end lang.classicalGeometry
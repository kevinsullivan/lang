import ...phys.src.classical_velocity
import .classical_geometry
import .classical_time

structure classicalVelocityVar : Type :=
mk :: (num : ℕ)

def classicalVelocityVarEq : classicalVelocityVar → classicalVelocityVar → bool
| v1 v2 := v1.num=v2.num

def classicalVelocityEnvironment := (classicalVelocityVar → classicalVelocity)

def init_classicalVelocityEnvironment := λ v : classicalTimeVar, worldTime

inductive classicalVelocityExpression : Type
| classicalVelocityLiteral (v : classicalVelocity)
| classicalVelocityVar (v : classicalVelocityVar)
| classicalVelocityExpr (g : classicalGeometryExpression) (t : classicalTimeExpression)
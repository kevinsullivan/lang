import ...phys.src.space

structure classicalVelocityVar : Type :=
mk :: (num : ℕ)

def classicalVelocityVarEq : classicalVelocityVar → classicalVelocityVar → bool
| v1 v2 := v1.num=v2.num


def classicalVelocityEnvironment := (classicalVelocityVar → Space.classicalVelocity)

inductive classicalVelocityExpression : Type
-- fill in constructors
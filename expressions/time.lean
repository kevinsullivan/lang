import ...phys.src.space

structure classicalTimeVar : Type :=
mk :: (num : ℕ) 

def classicalTimeVarEq : classicalTimeVar → classicalTimeVar → bool
| v1 v2 := v1.num=v2.num

def classicalTimeEnvironment := (classicalTimeVar → Space.classicalTime)

inductive classicalTimeExpression
| classicalTimeLiteral (V : Space.classicalTime) : classicalTimeExpression
| classicalTimeVariable (v : classicalTimeVar) : classicalTimeExpression


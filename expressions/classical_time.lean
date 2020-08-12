import ...phys.src.classical_time

structure classicalTimeVar : Type :=
mk :: (num : ℕ) 

def classicalTimeVarEq : classicalTimeVar → classicalTimeVar → bool
| v1 v2 := v1.num=v2.num

def classicalTimeEnvironment := (classicalTimeVar → classicalTime)

inductive classicalTimeExpression
| classicalTimeLiteral (v : classicalTime) : classicalTimeExpression
| classicalTimeVariable (v : classicalTimeVar) : classicalTimeExpression

def classicalTimeEval : classicalTimeExpression → classicalTimeEnvironment → classicalTime
| (classicalTimeExpression.classicalTimeLiteral V) E := V
| (classicalTimeExpression.classicalTimeVariable v) E := E v
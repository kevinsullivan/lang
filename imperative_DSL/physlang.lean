import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean


/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/

inductive cmd : Type
| skip
| classicalGeometryAssmt (v : classicalGeometryVar) (e : classicalGeometryExpression) 
| classicalTimeAssmt (v : classicalTimeVar) (e : classicalTimeExpression) 
| classicalVelocityAssmt (v : classicalVelocityVar) (e : classicalVelocityExpression)
| if_then_else (b : bExpr) (t f : cmd)
| seq (c1 c2 : cmd)

structure env : Type :=
mk ::   (g: classicalGeometryEnvironment)
        (t: classicalTimeEnvironment)
        (v: classicalVelocityEnvironment)

def init_env := env.mk 
                    init_classicalGeometryEnvironment
                    init_classicalTimeEnvironment
                    init_classicalVelocitEnvironment



-- TBD!
--Command Eval functions take in a command, an environment, and returns a new updated environment
--after assigning the new value to the variable 
def cmd_eval : cmd → env → env
| (cmd.classicalGeometryAssmt v e) i :=  
    λ (var : classicalGeometryVar),
        if (classicalGeometryVarEq v var) 
        then (classicalGeometryEval e E) 
        else (E var)
| (cmd.skip) E := E
| (cmd.classicalGeometrySeq c1 c2) E :=
    let i1 := cmd_eval c1 E in 
        cmd_eval c2 i1
| (cmd.classicalGeometryIf b c1 c2) E := 
    if b then (cmd_eval c1 E) else 
        (cmd_eval c2 E)

def classicalTimeCmd_eval : classicalTimeCmd → classicalTimeEnvironment → classicalTimeEnvironment 
| (classicalTimeCmd.classicalTimeAssmt v e) E :=
    λ (var : classicalTimeVar),
        if (classicalTimeVarEq v var) then (classicalTimeEval e E) else (E var)
| (classicalTimeCmd.skip) E := E
| (classicalTimeCmd.classicalTimeSeq c1 c2) E :=
    let i1 := classicalTimeCmd_eval c1 E in 
        classicalTimeCmd_eval c2 i1
| (classicalTimeCmd.classicalTimeIf b c1 c2) E := 
    if b then (classicalTimeCmd_eval c1 E) else 
        (classicalTimeCmd_eval c2 E)


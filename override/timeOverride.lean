import ..imperative_DSL.environment
import ..eval.timeEval

open lang.classicalTime

def assignTime : environment.env → lang.classicalTime.var → lang.classicalTime.expr → environment.env
| i v e := environment.env.mk i.g 
    (λ r,     
    if (varEq v r) 
        then (classicalTimeEval e i) 
        else (i.t r))
    i.v i.a
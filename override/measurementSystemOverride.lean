import ..imperative_DSL.environment
import ..eval.measurementEval

open lang.measurementSystem

def assignMeasurementSystem : environment.env → measureVar → measureExpr → environment.env
| i v e :=
                ⟨i.t,⟨(λ r,     
                if (measureVarEq v r) 
                then (measurementSystemEval e i) 
                else (i.ms.ms r))⟩⟩  
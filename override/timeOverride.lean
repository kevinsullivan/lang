import ..imperative_DSL.environment
import ..eval.timeEval

open lang.classicalTime

def assignTimeSpace : environment.env → lang.classicalTime.spaceVar → lang.classicalTime.spaceExpr → environment.env
| i v e :=
                ⟨⟨(λ r,     
                if (spaceVarEq v r) 
                then (classicalTimeEval e i) 
                else (i.t.sp r)),i.t.fr⟩, i.ms ⟩ 
                
def assignTimeFrame : environment.env → lang.classicalTime.frameVar → lang.classicalTime.frameExpr → environment.env
| i v e := 
               ⟨⟨i.t.sp,(λ r,     
                if (frameVarEq v r) 
                then (classicalTimeFrameEval e i) 
                else (i.t.fr r))⟩, i.ms⟩
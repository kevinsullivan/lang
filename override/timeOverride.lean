import ..imperative_DSL.environment
import ..eval.timeEval

open lang.classicalTime

def assignTimeSpace : environment.env → lang.classicalTime.spaceVar → lang.classicalTime.spaceExpr → environment.env
| i v e :=
                ⟨⟨(λ r,     
                if (spaceVarEq v r) 
                then (classicalTimeEval e i) 
                else (i.t.sp r)),i.t.fr, i.t.vec, i.t.pt⟩, i.ms ⟩ 
                
def assignTimeFrame : environment.env → lang.classicalTime.frameVar → lang.classicalTime.frameExpr → environment.env
| i v e := 
               ⟨⟨i.t.sp,(λ r,     
                if (frameVarEq v r) 
                then (classicalTimeFrameEval e i) 
                else (i.t.fr r)),i.t.vec,i.t.pt⟩, i.ms⟩

def assignTimeVector : environment.env → lang.classicalTime.CoordinateVectorVar → lang.classicalTime.CoordinateVectorExpr → environment.env 
| i v e := 
               ⟨⟨i.t.sp,i.t.fr,(λ r,     
                if (CoordinateVectorVarEq v r) 
                then (classicalTimeCoordinateVectorEval e i) 
                else (i.t.vec r)),i.t.pt⟩, i.ms⟩

def assignTimePoint : environment.env → lang.classicalTime.CoordinatePointVar → lang.classicalTime.CoordinatePointExpr → environment.env 
| i v e := 
               ⟨⟨i.t.sp,i.t.fr,i.t.vec,(λ r,     
                if (pointVarEq v r) 
                then (classicalTimeCoordinatePointEval e i) 
                else (i.t.pt r))⟩, i.ms⟩
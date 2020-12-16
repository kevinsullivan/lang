import ..imperative_DSL.environment
import ..eval.timeEval

open lang.classicalTime

def assignTimeSpace : environment.env → lang.classicalTime.spaceVar → lang.classicalTime.spaceExpr → environment.env
| i v e :=
                ⟨⟨(λ r,     
                if (spaceVarEq v r) 
                then (classicalTimeEval e i) 
                else (i.t.sp r)),i.t.fr, i.t.tr, i.t.vec, i.t.pt, i.t.s⟩, i.g, i.ms⟩ 
                
def assignTimeFrame : environment.env → lang.classicalTime.frameVar → lang.classicalTime.frameExpr → environment.env
| i v e := 
               ⟨⟨i.t.sp,(λ r,     
                if (frameVarEq v r) 
                then (classicalTimeFrameEval e i) 
                else (i.t.fr r)), i.t.tr,i.t.vec,i.t.pt, i.t.s⟩, i.g, i.ms⟩
                
def assignTimeTransform : environment.env → lang.classicalTime.transformVar → lang.classicalTime.transformExpr → environment.env
| i v e := 
               ⟨⟨i.t.sp,i.t.fr,(λ r,     
                if (transformVarEq v r) 
                then (classicalTimeTransformEval e i) 
                else (i.t.tr r)), i.t.vec,i.t.pt, i.t.s⟩, i.g, i.ms⟩

def assignTimeVector : environment.env → lang.classicalTime.CoordinateVectorVar → lang.classicalTime.CoordinateVectorExpr → environment.env 
| i v e := 
               ⟨⟨i.t.sp,i.t.fr, i.t.tr,(λ r,     
                if (CoordinateVectorVarEq v r) 
                then (classicalTimeCoordinateVectorEval e i) 
                else (i.t.vec r)),i.t.pt, i.t.s⟩, i.g, i.ms⟩

def assignTimePoint : environment.env → lang.classicalTime.CoordinatePointVar → lang.classicalTime.CoordinatePointExpr → environment.env 
| i v e := 
               ⟨⟨i.t.sp,i.t.fr, i.t.tr,i.t.vec,(λ r,     
                if (pointVarEq v r) 
                then (classicalTimeCoordinatePointEval e i) 
                else (i.t.pt r)), i.t.s⟩, i.g, i.ms⟩


def assignTimeScalar : environment.env → 
  lang.classicalTime.ScalarVar → 
  lang.classicalTime.ScalarExpr → environment.env 
| i v e := 
               ⟨⟨i.t.sp,i.t.fr, i.t.tr,i.t.vec,i.t.pt, (λ r,     
                if (scalarVarEq v r) 
                then (classicalTimeScalarEval e i) 
                else (i.t.s r))⟩, i.g, i.ms⟩
import ..imperative_DSL.environment
import ..eval.geometryEval

open lang.euclideanGeometry3

def assignGeometry3Space : environment.env → lang.euclideanGeometry3.spaceVar → lang.euclideanGeometry3.spaceExpr → environment.env
| i v e :=
                ⟨i.t,⟨(λ r,     
                if (spaceVarEq v r) 
                then (euclideanGeometry3Eval e i) 
                else (i.g.sp r)),i.g.fr, i.g.tr, i.g.vec, i.g.pt, i.g.s⟩, i.ms⟩ 
                
def assignGeometry3Frame : environment.env → lang.euclideanGeometry3.frameVar → lang.euclideanGeometry3.frameExpr → environment.env
| i v e := 
               ⟨i.t,⟨i.g.sp,(λ r,     
                if (frameVarEq v r) 
                then (euclideanGeometry3FrameEval e i) 
                else (i.g.fr r)),i.g.tr, i.g.vec,i.g.pt, i.g.s⟩, i.ms⟩

def assignGeometry3Transform : environment.env → lang.euclideanGeometry3.TransformVar → lang.euclideanGeometry3.TransformExpr → environment.env
| i v e := 
               ⟨i.t,⟨i.g.sp,i.g.fr,(λ r,     
                if (transformVarEq v r) 
                then (euclideanGeometry3TransformEval e i) 
                else (i.g.tr r)), i.g.vec,i.g.pt, i.g.s⟩, i.ms⟩



def assignGeometry3Vector : environment.env → lang.euclideanGeometry3.CoordinateVectorVar → lang.euclideanGeometry3.CoordinateVectorExpr → environment.env 
| i v e := 
               ⟨i.t,⟨i.g.sp,i.g.fr,i.g.tr,(λ r,     
                if (vectorVarEq v r) 
                then (euclideanGeometry3CoordinateVectorEval e i) 
                else (i.g.vec r)),i.g.pt, i.g.s⟩, i.ms⟩

def assignGeometry3Point : environment.env → lang.euclideanGeometry3.CoordinatePointVar → lang.euclideanGeometry3.CoordinatePointExpr → environment.env 
| i v e := 
               ⟨i.t,⟨i.g.sp,i.g.fr,i.g.tr,i.g.vec,(λ r,     
                if (pointVarEq v r) 
                then (euclideanGeometry3CoordinatePointEval e i) 
                else (i.g.pt r)), i.g.s⟩, i.ms⟩


def assignGeometry3Scalar : environment.env → 
  lang.euclideanGeometry3.ScalarVar → 
  lang.euclideanGeometry3.ScalarExpr → environment.env 
| i v e := 
               ⟨i.t,⟨i.g.sp,i.g.fr,i.g.tr,i.g.vec,i.g.pt, (λ r,     
                if (scalarVarEq v r) 
                then (euclideanGeometry3ScalarEval e i) 
                else (i.g.s r))⟩, i.ms⟩
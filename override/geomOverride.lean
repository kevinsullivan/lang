import ..imperative_DSL.environment
import ..eval.geometryEval
open lang.classicalGeometry

def assignGeometry : environment.env → lang.classicalGeometry.var → lang.classicalGeometry.expr → environment.env
| i v e := environment.env.mk 
    (λ r,     
    if (varEq v r) 
        then (classicalGeometryEval e i) 
        else (i.g r)) 
    i.t i.v i.a
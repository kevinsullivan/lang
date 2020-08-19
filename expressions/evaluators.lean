import ..imperative_DSL.environment

open lang.classicalVelocity
def classicalVelocityEval : lang.classicalVelocity.expr → environment.env → classicalVelocity 
| (expr.lit v) i := v
| (lang.classicalVelocity.expr.var v) i := i.v v
| (expr.div g t) i := 
    match g with
    | (lang.classicalGeometry.expr.lit e) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalVelocity.mk 0 e e2
        | (lang.classicalTime.expr.var v2) := 
            classicalVelocity.mk 0 (e) (i.t v2)
        end
    | (lang.classicalGeometry.expr.var v) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalVelocity.mk 0 (i.g v) (e2)
        | (lang.classicalTime.expr.var v2) := classicalVelocity.mk 0 (i.g v) (i.t v2)
        end
    end

def assignVelocity : environment.env → lang.classicalVelocity.var → lang.classicalVelocity.expr → environment.env
| i v e := environment.env.mk i.g i.t 
    (λ r,     if (varEq v r) 
        then (classicalVelocityEval e i) 
        else (i.v r))

open lang.classicalTime

def classicalTimeEval : lang.classicalTime.expr → environment.env → classicalTime
| (lang.classicalTime.expr.lit V) i := V
| (lang.classicalTime.expr.var v) i := i.t v

def assignTime : environment.env → lang.classicalTime.var → lang.classicalTime.expr → environment.env
| i v e := environment.env.mk i.g 
    (λ r,     
    if (varEq v r) 
        then (classicalTimeEval e i) 
        else (i.t r))
    i.v 
    

open lang.classicalGeometry

def classicalGeometryEval : lang.classicalGeometry.expr → environment.env → classicalGeometry 
| (lang.classicalGeometry.expr.lit s) i := s
| (lang.classicalGeometry.expr.var v) i := i.g v


def assignGeometry : environment.env → lang.classicalGeometry.var → lang.classicalGeometry.expr → environment.env
| i v e := environment.env.mk 
    (λ r,     
    if (varEq v r) 
        then (classicalGeometryEval e i) 
        else (i.g r)) 
    i.t i.v
    
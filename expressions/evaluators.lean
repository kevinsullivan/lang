import ..imperative_DSL.environment

open lang.classicalVelocity
def evalVelocity : lang.classicalVelocity.expr → environment.env → classicalVelocity 
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

def overrideVelocity : environment.env → lang.classicalVelocity.var → lang.classicalVelocity.expr → environment.env
| i v e := environment.env.mk i.g i.t 
    (λ r,     if (varEq v r) 
        then (evalVelocity e i) 
        else (i.v r))

open lang.classicalTime

def evalTime : lang.classicalTime.expr → environment.env → classicalTime
| (lang.classicalTime.expr.lit V) i := V
| (lang.classicalTime.expr.var v) i := i.t v

def overrideTime : environment.env → lang.classicalTime.var → lang.classicalTime.expr → environment.env
| i v e := environment.env.mk i.g 
    (λ r,     
    if (varEq v r) 
        then (evalTime e i) 
        else (i.t r))
    i.v 
    

open lang.classicalGeometry

def evalGeometry : lang.classicalGeometry.expr → environment.env → classicalGeometry 
| (lang.classicalGeometry.expr.lit s) i := s
| (lang.classicalGeometry.expr.var v) i := i.g v


def overrideGeometry : environment.env → lang.classicalGeometry.var → lang.classicalGeometry.expr → environment.env
| i v e := environment.env.mk 
    (λ r,     
    if (varEq v r) 
        then (evalGeometry e i) 
        else (i.g r)) 
    i.t i.v
    
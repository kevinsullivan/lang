import ..imperative_DSL.environment

open lang.classicalGeometry

def classicalGeometryEval : lang.classicalGeometry.expr → environment.env → classicalGeometry 
| (lang.classicalGeometry.expr.lit s) i := s
| (lang.classicalGeometry.expr.var v) i := i.g v


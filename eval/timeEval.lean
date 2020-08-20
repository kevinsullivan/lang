import ..imperative_DSL.environment


open lang.classicalTime

def classicalTimeEval : lang.classicalTime.expr → environment.env → classicalTime
| (lang.classicalTime.expr.lit V) i := V
| (lang.classicalTime.expr.var v) i := i.t v


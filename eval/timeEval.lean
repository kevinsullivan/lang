import ..imperative_DSL.environment


open lang.classicalTime

def classicalTimeEval : lang.classicalTime.spaceExpr → environment.env → classicalTime
| (lang.classicalTime.spaceExpr.lit V) i := V
| (lang.classicalTime.spaceExpr.var v) i := i.t.sp v

def classicalTimeFrameEval : lang.classicalTime.frameExpr → environment.env → classicalTimeFrame
| (lang.classicalTime.frameExpr.lit V) i := V
| (lang.classicalTime.frameExpr.var v) i := i.t.fr v


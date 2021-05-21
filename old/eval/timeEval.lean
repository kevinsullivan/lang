import ..imperative_DSL.environment


open lang.classicalTime

open measurementSystem

attribute [reducible]
def classicalTimeEval : lang.classicalTime.spaceExpr → environment.env → classicalTime
| (lang.classicalTime.spaceExpr.lit V) i := V
| (lang.classicalTime.spaceExpr.var v) i := i.t.sp v

attribute [reducible]
def classicalTimeFrameEval (sp : classicalTime) 
    : lang.classicalTime.frameExpr sp → environment.env → classicalTimeFrame sp
| (lang.classicalTime.frameExpr.lit V) i := V
| (lang.classicalTime.frameExpr.var v) i := i.t.fr sp v

attribute [reducible]
def classicalTimeTransformEval (sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s) 
    : lang.classicalTime.TransformExpr sig → environment.env → classicalTimeTransform sig.2.1 sig.2.2
| (lang.classicalTime.TransformExpr.lit V) i := V
| (lang.classicalTime.TransformExpr.var v) i := i.t.tr sig v

attribute [reducible]
def classicalTimeQuantityEval
    (sig: Σs : classicalTime, MeasurementSystem) 
    : lang.classicalTime.QuantityExpr sig → environment.env → classicalTimeQuantity sig.1 sig.2
| (lang.classicalTime.QuantityExpr.lit V) i := V
| (lang.classicalTime.QuantityExpr.var v) i := i.t.q sig v

attribute [reducible]
def classicalTimeCoordinateVectorEval
    (sig: Σs : classicalTime, classicalTimeFrame s)
         : lang.classicalTime.CoordinateVectorExpr sig → environment.env → classicalTimeCoordinateVector sig.2
| (lang.classicalTime.CoordinateVectorExpr.lit V) i := V
| (lang.classicalTime.CoordinateVectorExpr.var v) i := i.t.vec sig v


attribute [reducible]
def classicalTimeCoordinatePointEval
    (sig: Σs : classicalTime, classicalTimeFrame s) : 
    lang.classicalTime.CoordinatePointExpr sig → environment.env → classicalTimeCoordinatePoint sig.2
| (lang.classicalTime.CoordinatePointExpr.lit V) i := V
| (lang.classicalTime.CoordinatePointExpr.var v) i := i.t.pt sig v
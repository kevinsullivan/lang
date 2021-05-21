import ..imperative_DSL.environment


open lang.euclideanGeometry
open measurementSystem

attribute [reducible]
def euclideanGeometryEval {n : ℕ} 
    : lang.euclideanGeometry.spaceExpr n → environment.env → euclideanGeometry n
| (lang.euclideanGeometry.spaceExpr.lit V) i := V
| (lang.euclideanGeometry.spaceExpr.var v) i := i.g.sp n v

attribute [reducible]
def euclideanGeometryFrameEval (sig : Σn:ℕ, euclideanGeometry n)
    : lang.euclideanGeometry.frameExpr sig → environment.env → euclideanGeometryFrame sig.2
| (lang.euclideanGeometry.frameExpr.lit V) i := V
| (lang.euclideanGeometry.frameExpr.var v) i := i.g.fr sig v

attribute [reducible]
def euclideanGeometryTransformEval 
    (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s))
: lang.euclideanGeometry.TransformExpr sig
    → environment.env → euclideanGeometryTransform sig.2.2.1 sig.2.2.2
| (lang.euclideanGeometry.TransformExpr.lit V) i := V
| (lang.euclideanGeometry.TransformExpr.var v) i := i.g.tr sig v

attribute [reducible]
def euclideanGeometryQuantityEval 
    (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem)
    -- {n : ℕ} {sp : euclideanGeometry n} {m : measurementSystem.MeasurementSystem} 
    : lang.euclideanGeometry.QuantityExpr sig → 
        environment.env → 
            euclideanGeometryQuantity sig.snd.fst sig.snd.snd
| (lang.euclideanGeometry.QuantityExpr.lit V) i := V
| (lang.euclideanGeometry.QuantityExpr.var v) i := i.g.q sig v--n sp m v


attribute [reducible]
def euclideanGeometryAngleEval (sig : Σn:ℕ, euclideanGeometry n)
    : lang.euclideanGeometry.AngleExpr sig → environment.env → euclideanGeometryAngle sig.snd
| (lang.euclideanGeometry.AngleExpr.lit V) i := V
| (lang.euclideanGeometry.AngleExpr.var v) i := i.g.a sig v

attribute [reducible]
def euclideanGeometryOrientationEval (sig : Σn:ℕ, euclideanGeometry n)
    : lang.euclideanGeometry.OrientationExpr sig → environment.env → euclideanGeometryOrientation sig.snd
| (lang.euclideanGeometry.OrientationExpr.lit V) i := V
| (lang.euclideanGeometry.OrientationExpr.var v) i := i.g.or sig v

attribute [reducible]
def euclideanGeometryRotationEval (sig : Σn:ℕ, euclideanGeometry n)
    : lang.euclideanGeometry.RotationExpr sig → environment.env → euclideanGeometryRotation sig.snd 
| (lang.euclideanGeometry.RotationExpr.lit V) i := V
| (lang.euclideanGeometry.RotationExpr.var v) i := i.g.r sig v

attribute [reducible]
def euclideanGeometryCoordinateVectorEval (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)
    : lang.euclideanGeometry.CoordinateVectorExpr sig → environment.env → euclideanGeometryCoordinateVector sig.snd.snd
| (lang.euclideanGeometry.CoordinateVectorExpr.lit V) i := V
| (lang.euclideanGeometry.CoordinateVectorExpr.var v) i := i.g.vec sig v


attribute [reducible]
def euclideanGeometryCoordinatePointEval (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)
    : lang.euclideanGeometry.CoordinatePointExpr sig → environment.env → euclideanGeometryCoordinatePoint sig.snd.snd
| (lang.euclideanGeometry.CoordinatePointExpr.lit V) i := V
| (lang.euclideanGeometry.CoordinatePointExpr.var v) i := i.g.pt sig v


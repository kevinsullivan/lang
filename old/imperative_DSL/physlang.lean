import .environment
--import ..eval.accelerationEval
--import ..eval.geometryEval
--import ..eval.timeEval
--import ..eval.velocityEval
import ..expressions.measurementSystem
import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_hertz
import ..expressions.classical_luminous_intensity
--import ..expressions.classical_velocity
--import ..expressions.classical_acceleration
import ..override.geomOverride
import ..override.timeOverride
import ..override.hertzOverride
import ..override.luminousIntensityOverride
import ..override.measurementSystemOverride
import ..override.axisOrientationOverride
--import ..override.velocityOverride
--import ..override.accelerationOverride
import ..expressions.boolean

import linear_algebra.affine_space.basic

universes u
/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/
open measurementSystem
open 


inductive cmd : Type
| skip 
| classicalTimeAssmt 
    (v : lang.classicalTime.spaceVar) 
    (e : lang.classicalTime.spaceExpr) 
| classicalTimeExpr
    (e : lang.classicalTime.spaceExpr) 
| classicalTimeFrameAssmt 
    ( sp : classicalTime ) 
    (v : lang.classicalTime.frameVar sp) 
    (e : lang.classicalTime.frameExpr sp)
| classicalTimeFrameExpr 
    { sp : classicalTime } (e : lang.classicalTime.frameExpr sp)
| classicalTimeTransformAssmt
    (sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s)
        (v : lang.classicalTime.TransformVar sig)
        (e : lang.classicalTime.TransformExpr sig)
| classicalTimeTransformExpr
    {sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s} 
        (e : lang.classicalTime.TransformExpr sig)
| classicalTimeQuantityAssmt
    (sig: Σs : classicalTime, MeasurementSystem)
        (v : lang.classicalTime.QuantityVar sig)
        (e : lang.classicalTime.QuantityExpr sig)
| classicalTimeQuantityExpr
    {sig: Σs : classicalTime, MeasurementSystem}
        (e : lang.classicalTime.QuantityExpr sig)
| classicalTimeCoordinatePointAssmt 
    (sig: Σs : classicalTime, classicalTimeFrame s)
        (v : lang.classicalTime.CoordinatePointVar sig) 
        (e : lang.classicalTime.CoordinatePointExpr sig)
| classicalTimeCoordinatePointExpr
    {sig: Σs : classicalTime, classicalTimeFrame s}
        (e : lang.classicalTime.CoordinatePointExpr sig)
| classicalTimeCoordinateVectorAssmt 
    (sig: Σs : classicalTime, classicalTimeFrame s)
        (v : lang.classicalTime.CoordinateVectorVar sig) 
        (e : lang.classicalTime.CoordinateVectorExpr sig)
| classicalTimeCoordinateVectorExpr
    {sig: Σs : classicalTime, classicalTimeFrame s}
        (e : lang.classicalTime.CoordinateVectorExpr sig)
| euclideanGeometryAssmt 
    (n : ℕ)
        (v : lang.euclideanGeometry.spaceVar n) 
        (e : lang.euclideanGeometry.spaceExpr n) 
| euclideanGeometryExpr 
    {n : ℕ}
        (e : lang.euclideanGeometry.spaceExpr n) 
| euclideanGeometryFrameAssmt 
    (sig : Σn:ℕ, euclideanGeometry n)
        (v : lang.euclideanGeometry.frameVar sig) 
        (e : lang.euclideanGeometry.frameExpr sig)
| euclideanGeometryFrameExpr 
    {sig : Σn:ℕ, euclideanGeometry n}
        (e : lang.euclideanGeometry.frameExpr sig)
| euclideanGeometryTransformAssmt
    (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s))
        (v : lang.euclideanGeometry.TransformVar sig)
        (e : lang.euclideanGeometry.TransformExpr sig)
| euclideanGeometryTransformExpr
    {sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s)}
        (e : lang.euclideanGeometry.TransformExpr sig)
| euclideanGeometryQuantityAssmt
    (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem)
        (v : lang.euclideanGeometry.QuantityVar sig)
        (e : lang.euclideanGeometry.QuantityExpr sig)
| euclideanGeometryQuantityExpr
    {sig : Σn, Σs: euclideanGeometry n,MeasurementSystem}
        (e : lang.euclideanGeometry.QuantityExpr sig)
| euclideanGeometryAngleAssmt
    (sig : Σn:ℕ, euclideanGeometry n)
        (v : lang.euclideanGeometry.AngleVar sig)
        (e : lang.euclideanGeometry.AngleExpr sig)
| euclideanGeometryAngleExpr
    {sig : Σn:ℕ, euclideanGeometry n}
        (e : lang.euclideanGeometry.AngleExpr sig)
| euclideanGeometryOrientationAssmt
    (sig : Σn:ℕ, euclideanGeometry n)
        (v : lang.euclideanGeometry.OrientationVar sig)
        (e : lang.euclideanGeometry.OrientationExpr sig)
| euclideanGeometryOrientationExpr
    {sig : Σn:ℕ, euclideanGeometry n}
        (e : lang.euclideanGeometry.OrientationExpr sig)
| euclideanGeometryRotationAssmt
    (sig : Σn:ℕ, euclideanGeometry n)
        (v : lang.euclideanGeometry.RotationVar sig)
        (e : lang.euclideanGeometry.RotationExpr sig)
| euclideanGeometryRotationExpr
    {sig : Σn:ℕ, euclideanGeometry n}
        (e : lang.euclideanGeometry.RotationExpr sig)
| euclideanGeometryCoordinatePointAssmt 
    (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)
        (v : lang.euclideanGeometry.CoordinatePointVar sig) 
        (e : lang.euclideanGeometry.CoordinatePointExpr sig)
| euclideanGeometryCoordinatePointExpr
    {sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s}
        (e : lang.euclideanGeometry.CoordinatePointExpr sig)
| euclideanGeometryCoordinateVectorAssmt 
    (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)
        (v : lang.euclideanGeometry.CoordinateVectorVar sig) 
        (e : lang.euclideanGeometry.CoordinateVectorExpr sig)
| euclideanGeometryCoordinateVectorExpr 
    {sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s}
        (e : lang.euclideanGeometry.CoordinateVectorExpr sig)
/-| classicalHertzAssmt 
    (v : lang.classicalHertz.spaceVar) 
    (e : lang.classicalHertz.spaceExpr) 
| classicalHertzExpr
    (e : lang.classicalHertz.spaceExpr) 
| classicalHertzQuantityAssmt
    (v : lang.classicalHertz.QuantityVar)
    (e : lang.classicalHertz.QuantityExpr)
| classicalHertzQuantityExpr
    (e : lang.classicalHertz.QuantityExpr)
| classicalLuminousIntensityAssmt 
    (v : lang.classicalLuminousIntensity.spaceVar) 
    (e : lang.classicalLuminousIntensity.spaceExpr) 
| classicalLuminousIntensityExpr
    (e : lang.classicalLuminousIntensity.spaceExpr) 
| classicalLuminousIntensityQuantityAssmt
    (v : lang.classicalLuminousIntensity.QuantityVar)
    (e : lang.classicalLuminousIntensity.QuantityExpr)
| classicalLuminousIntensityQuantityExpr
    (e : lang.classicalLuminousIntensity.QuantityExpr)-/
| measurementSystemAssmt 
    (v : lang.measurementSystem.measureVar) 
    (e : lang.measurementSystem.measureExpr)
| measurementSystemExpr
    (e : lang.measurementSystem.measureExpr)
| axisOrientationAssmt 
    (v : lang.axisOrientation.orientationVar) 
    (e : lang.axisOrientation.orientationExpr)
| axisOrientationExpr
    (e : lang.axisOrientation.orientationExpr)
| while 
    (b : bExpr) 
    (d : cmd) -- this is not correct and requires more careful attention
| try_catch
    (t : cmd)
    (c : cmd)
| if_then_else 
    (b : bExpr) 
    (t e : cmd)
| for 
    (b : bExpr) -- what goes here?
    (d : cmd)
| seq (c1 c2 : cmd)

notation one;two := cmd.seq one two
notation; := cmd.skip
notation `while `b,d := cmd.while b d
notation `try `t,`catch `c := cmd.try_catch t c
notation `for `b,d := cmd.for b d

--time
notation v=e := cmd.classicalTimeAssmt v e
notation`expr `e := cmd.classicalTimeExpr e
notation v=e := cmd.classicalTimeFrameAssmt v e
notation`expr `e := cmd.classicalTimeFrameExpr e
notation v=e := cmd.classicalTimeTransformAssmt v e
notation`expr `e := cmd.classicalTimeTransformExpr e
notation v=e := cmd.classicalTimeQuantityAssmt v e
notation`expr `e := cmd.classicalTimeQuantityExpr e
notation v=e := cmd.classicalTimeCoordinatePointAssmt v e
notation`expr `e := cmd.classicalTimeCoordinatePointExpr e
notation v=e := cmd.classicalTimeCoordinateVectorAssmt v e
notation`expr `e := cmd.classicalTimeCoordinateVectorExpr e

--geom
notation v=e := cmd.euclideanGeometryAssmt v e
notation`expr `e := cmd.euclideanGeometryExpr e
notation v=e := cmd.euclideanGeometryFrameAssmt v e
notation`expr `e := cmd.euclideanGeometryFrameExpr e
notation v=e := cmd.euclideanGeometryTransformAssmt v e
notation`expr `e := cmd.euclideanGeometryTransformExpr e
notation v=e := cmd.euclideanGeometryQuantityAssmt v e
notation`expr `e := cmd.euclideanGeometryQuantityExpr e
notation v=e := cmd.euclideanGeometryAngleAssmt v e
notation`expr `e := cmd.euclideanGeometryAngleExpr e
notation v=e := cmd.euclideanGeometryOrientationAssmt v e
notation`expr `e := cmd.euclideanGeometryOrientationExpr e
notation v=e := cmd.euclideanGeometryRotationAssmt v e
notation`expr `e := cmd.euclideanGeometryRotationExpr e
notation v=e := cmd.euclideanGeometryCoordinatePointAssmt v e
notation`expr `e := cmd.euclidenaGeometryCoordinatePointExpr e
notation v=e := cmd.euclideanGeometryCoordinateVectorAssmt v e
notation`expr `e := cmd.euclideanGeometryCoordinateVectorExpr e

/-
notation v=e := cmd.classicalHertzAssmt v e
notation`expr `e := cmd.classicalHertzExpr e
notation v=e := cmd.classicalHertzQuantityAssmt v e
notation `expr `e := cmd.classicalHertzQuantityExpr e
notation v=e := cmd.classicalLuminousIntensityAssmt v e
notation`expr `e := cmd.classicalLuminousIntensityExpr e
notation v=e := cmd.classicalLuminousIntensityQuantityAssmt v e
notation `expr `e := cmd.classicalLuminousIntensityQuantityExpr e
-/

notation v=e := cmd.measurementSystemAssmt v e
notation v=e := cmd.axisOrientationAssmt v e
notation `skip` := cmd.skip


open cmd 

noncomputable def cmdEval : cmd → environment.env → environment.env
/-| (classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr)) i := 
    assignGeometry i v e-/
| skip i := i
| (classicalTimeAssmt v e) i := assignTimeSpace i v e
| (classicalTimeExpr e) i := i
| (classicalTimeFrameAssmt sp v e) i := assignTimeFrame sp i v e
| (classicalTimeFrameExpr e) i := i
| (classicalTimeTransformAssmt sig v e) i := assignTimeTransform sig i v e
| (classicalTimeTransformExpr e) i := i
| (classicalTimeQuantityAssmt sig v e) i := assignTimeQuantity sig i v e
| (classicalTimeQuantityExpr e) i := i
| (classicalTimeCoordinatePointAssmt sig v e) i := assignTimePoint sig i v e
| (classicalTimeCoordinatePointExpr e) i := i
| (classicalTimeCoordinateVectorAssmt sig v e) i := assignTimeVector sig i v e
| (classicalTimeCoordinateVectorExpr e) i := i
| (euclideanGeometryAssmt sig v e) i := assignGeometrySpace sig i v e
| (euclideanGeometryExpr e) i := i
| (euclideanGeometryFrameAssmt sig v e) i := assignGeometryFrame sig i v e
| (euclideanGeometryFrameExpr e) i := i
| (euclideanGeometryTransformAssmt sig v e) i := assignGeometryTransform sig i v e
| (euclideanGeometryTransformExpr e) i := i
| (euclideanGeometryQuantityAssmt sig v e) i := assignGeometryQuantity sig i v e
| (euclideanGeometryQuantityExpr e) i := i
| (euclideanGeometryAngleAssmt sig v e) i := assignGeometryAngle sig i v e
| (euclideanGeometryAngleExpr e) i := i
| (euclideanGeometryOrientationAssmt sig v e) i := assignGeometryOrientation sig i v e
| (euclideanGeometryOrientationExpr e) i := i
| (euclideanGeometryRotationAssmt sig v e) i := assignGeometryRotation sig i v e
| (euclideanGeometryRotationExpr e) i := i
| (euclideanGeometryCoordinatePointAssmt sig v e) i := assignGeometryPoint sig i v e
| (euclideanGeometryCoordinatePointExpr e) i := i
| (euclideanGeometryCoordinateVectorAssmt sig v e) i := assignGeometryVector sig i v e
| (euclideanGeometryCoordinateVectorExpr e) i := i
/-| (classicalHertzAssmt v e) i := assignHertzSpace i v e
| (classicalHertzExpr e) i := i 
| (classicalHertzQuantityAssmt v e) i := assignHertzQuantity i v e
| (classicalHertzQuantityExpr e) i := i
| (classicalLuminousIntensityAssmt v e) i := assignLuminousIntensitySpace i v e
| (classicalLuminousIntensityExpr e) i := i 
| (classicalLuminousIntensityQuantityAssmt v e) i := assignLuminousIntensityQuantity i v e
| (classicalLuminousIntensityQuantityExpr e) i := i-/
| (measurementSystemAssmt v e) i := assignMeasurementSystem i v e
| (measurementSystemExpr e) i := i
| (axisOrientationAssmt v e) i := assignAxisOrientation i v e
| (axisOrientationExpr e) i := i
| (try_catch t c) i := i
| (cmd.while b d) i := i--cmdEval d i -- this is not correct, but this is what it is for now.
| (cmd.for b d) i := i
| (cmd.if_then_else (b : bExpr)  (t : cmd) (f : cmd)) i := i --this is also incorrect? 1/21/20
    --if (bEval b bI) then (cmdEval t i) else (cmdEval f i) - BEN AND YANNI FILL IN --1/21/20 this is somewhat trickier
| (seq (c1 : cmd) (c2 : cmd)) i0 := 
    let i1 := cmdEval c1 i0 in 
    cmdEval c2 i1

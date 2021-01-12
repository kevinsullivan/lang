import .environment
--import ..eval.accelerationEval
--import ..eval.geometryEval
--import ..eval.timeEval
--import ..eval.velocityEval
import ..expressions.measurementSystem
import ..expressions.classical_geometry
import ..expressions.classical_time
--import ..expressions.classical_velocity
--import ..expressions.classical_acceleration
import ..override.geomOverride
import ..override.timeOverride
import ..override.measurementSystemOverride
--import ..override.velocityOverride
--import ..override.accelerationOverride
import ..expressions.boolean


/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/

inductive cmd : Type
--| classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr) 
| classicalTimeAssmt 
    (v : lang.classicalTime.spaceVar) 
    (e : lang.classicalTime.spaceExpr) 
| classicalTimeFrameAssmt 
    (v : lang.classicalTime.frameVar) 
    (e : lang.classicalTime.frameExpr)
| classicalTimeTransformAssmt
    (v : lang.classicalTime.transformVar)
    (e : lang.classicalTime.transformExpr)
| classicalTimeScalarAssmt
    (v : lang.classicalTime.ScalarVar)
    (e : lang.classicalTime.ScalarExpr)
| classicalTimeCoordinatePointAssmt 
    (v : lang.classicalTime.CoordinatePointVar) 
    (e : lang.classicalTime.CoordinatePointExpr)
| classicalTimeCoordinateVectorAssmt 
    (v : lang.classicalTime.CoordinateVectorVar) 
    (e : lang.classicalTime.CoordinateVectorExpr)
| euclideanGeometry3Assmt 
    (v : lang.euclideanGeometry3.spaceVar) 
    (e : lang.euclideanGeometry3.spaceExpr) 
| euclideanGeometry3FrameAssmt 
    (v : lang.euclideanGeometry3.frameVar) 
    (e : lang.euclideanGeometry3.frameExpr)
| euclideanGeometry3TransformAssmt
    (v : lang.euclideanGeometry3.TransformVar)
    (e : lang.euclideanGeometry3.TransformExpr)
| euclideanGeometry3ScalarAssmt
    (v : lang.euclideanGeometry3.ScalarVar)
    (e : lang.euclideanGeometry3.ScalarExpr)
| euclideanGeometry3AngleAssmt
    (v : lang.euclideanGeometry3.AngleVar)
    (e : lang.euclideanGeometry3.AngleExpr)
| euclideanGeometry3CoordinatePointAssmt 
    (v : lang.euclideanGeometry3.CoordinatePointVar) 
    (e : lang.euclideanGeometry3.CoordinatePointExpr)
| euclideanGeometry3CoordinateVectorAssmt 
    (v : lang.euclideanGeometry3.CoordinateVectorVar) 
    (e : lang.euclideanGeometry3.CoordinateVectorExpr)
| measurementSystemAssmt 
    (v : lang.measurementSystem.measureVar) 
    (e : lang.measurementSystem.measureExpr)



--| classicalVelocityAssmt (v : lang.classicalVelocity.var) (e : lang.classicalVelocity.expr)
--| classicalAccelerationAssmt (a : lang.classicalAcceleration.var) (e : lang.classicalAcceleration.expr)
| if_then_else (b : bExpr) (t f : cmd)
| seq (c1 c2 : cmd)
        
open cmd 

def cmdEval : cmd → environment.env → environment.env
/-| (classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr)) i := 
    assignGeometry i v e-/
| (classicalTimeAssmt v e) i := assignTimeSpace i v e
| (classicalTimeFrameAssmt v e) i := assignTimeFrame i v e
| (classicalTimeTransformAssmt v e) i := assignTimeTransform i v e
| (classicalTimeScalarAssmt v e) i := assignTimeScalar i v e
| (classicalTimeCoordinatePointAssmt v e) i := assignTimePoint i v e
| (classicalTimeCoordinateVectorAssmt v e) i := assignTimeVector i v e
| (euclideanGeometry3Assmt v e) i := assignGeometry3Space i v e
| (euclideanGeometry3FrameAssmt v e) i := assignGeometry3Frame i v e
| (euclideanGeometry3TransformAssmt v e) i := assignGeometry3Transform i v e
| (euclideanGeometry3ScalarAssmt v e) i := assignGeometry3Scalar i v e
| (euclideanGeometry3AngleAssmt v e) i := assignGeometry3Angle i v e
| (euclideanGeometry3CoordinatePointAssmt v e) i := assignGeometry3Point i v e
| (euclideanGeometry3CoordinateVectorAssmt v e) i := assignGeometry3Vector i v e
| (measurementSystemAssmt v e) i := assignMeasurementSystem i v e
/-| (classicalVelocityAssmt (v : lang.classicalVelocity.var) (e : lang.classicalVelocity.expr)) i := 
    assignVelocity i v e
| (classicalAccelerationAssmt (v : lang.classicalAcceleration.var) (e : lang.classicalAcceleration.expr)) i :=
    assignAcceleration i v e-/
| (if_then_else (b : bExpr)  (t : cmd) (f : cmd)) i := 
    i
    --if (bEval b bI) then (cmdEval t i) else (cmdEval f i) - BEN AND YANNI FILL IN
| (seq (c1 : cmd) (c2 : cmd)) i0 := 
    let i1 := cmdEval c1 i0 in cmdEval c2 i1

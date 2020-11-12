import .environment
--import ..eval.accelerationEval
--import ..eval.geometryEval
--import ..eval.timeEval
--import ..eval.velocityEval
import ..expressions.measurementSystem
--import ..expressions.classical_geometry
import ..expressions.classical_time
--import ..expressions.classical_velocity
--import ..expressions.classical_acceleration
--import ..override.geomOverride
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
| classicalTimeAssmt (v : lang.classicalTime.spaceVar) (e : lang.classicalTime.spaceExpr) 
| classicalTimeFrameAssmt (f : lang.classicalTime.frameVar) (e : lang.classicalTime.frameExpr)
| measurementSystemAssmt (v : lang.measurementSystem.measureVar) (e : lang.measurementSystem.measureExpr)
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

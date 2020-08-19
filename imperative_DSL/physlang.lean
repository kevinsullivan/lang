import .environment
import ..expressions.evaluators
import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean


/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/

inductive cmd : Type
| classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr) 
| classicalTimeAssmt (v : lang.classicalTime.var) (e : lang.classicalTime.expr) 
| classicalVelocityAssmt (v : lang.classicalVelocity.var) (e : lang.classicalVelocity.expr)
| if_then_else (b : bExpr) (t f : cmd)
| seq (c1 c2 : cmd)
        
open cmd 

def cmdEval : cmd → environment.env → environment.env
| (classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr)) i := 
    assignGeometry i v e
| (classicalTimeAssmt (v : lang.classicalTime.var) (e : lang.classicalTime.expr)) i := 
    assignTime i v e
| (classicalVelocityAssmt (v : lang.classicalVelocity.var) (e : lang.classicalVelocity.expr)) i := 
    assignVelocity i v e
| (if_then_else (b : bExpr)  (t : cmd) (f : cmd)) i := 
    i
    --if (bEval b bI) then (cmdEval t i) else (cmdEval f i) - BEN AND YANNI FILL IN
| (seq (c1 : cmd) (c2 : cmd)) i0 := 
    let i1 := cmdEval c1 i0 in cmdEval c2 i1

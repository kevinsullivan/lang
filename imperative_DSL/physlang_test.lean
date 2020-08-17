import .physlang
import .environment
import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
/-
Test code
-/
def g1 := lang.classicalGeometry.var.mk 0
def g2 := lang.classicalGeometry.var.mk 1

--default environments
def geomDefaultEnv : env := env.mk
    (λ v, classicalGeometry.mk 0 3)
    (λ v, classicalTime.mk 0)
    (λ v, classicalVelocity.mk 0 (classicalGeometry.mk 0 3) (classicalTime.mk 0))


def my_var : lang.classicalGeometry.var := lang.classicalGeometry.var.mk 0
def myProgram : cmd := cmd.classicalGeometryAssmt my_var (lang.classicalGeometry.expr.lit (classicalGeometry.mk 0 3))
#eval cmdEval myProgram geomDefaultEnv
 

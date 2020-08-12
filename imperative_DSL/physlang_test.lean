import .physlang

/-
Test code
-/
def g1 := classicalGeometryVar.mk 0
def g2 := classicalGeometryVar.mk 1

--default environments
def geomDefaultEnv : classicalGeometryEnvironment := λ v, classicalGeometry.mk 0 3
def timeDefaultEnv : classicalTimeEnvironment := λ v, classicalTime.mk 0

def my_var : classicalGeometryVar := classicalGeometryVar.mk 0
def myProgram : cmd := cmd.classicalGeometryAssmt my_var (classicalGeometryExpression.GeometricSpaceLiteral (Space.classicalGeometry.mk "" 3))
#eval cmd_eval myProgram geomDefaultEnv
 
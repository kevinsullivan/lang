--will import these later, temporary structures
inductive geomSpace : Type
| mk (dim : ℕ) : geomSpace

inductive timeSpace : Type
| mk

--variable types
structure geomSpaceVar : Type := 
mk :: (num : ℕ) 

structure timeSpaceVar : Type :=
mk :: (num : ℕ) 

--GeometricSpaceExpression
--Can be a literal, a variable, or function application expression
inductive GeometricSpaceExpression
| GeometricSpaceLiteral (V : geomSpace) : GeometricSpaceExpression
| GeometricSpaceVariable (v : geomSpaceVar) : GeometricSpaceExpression
| GeometricSpaceFunctionApp (V1 V2 : geomSpace) : GeometricSpaceExpression

--Same for time spaces
inductive TimeSpaceExpression
| TimeSpaceLiteral (V : timeSpace) : TimeSpaceExpression
| TimeSpaceVariable (v : timeSpaceVar) : TimeSpaceExpression
| TimeSpaceFunctionApp (V1 V2 : timeSpace) : TimeSpaceExpression

--geometric Space Commands
--a geomSpaceAssmt takes in a geom space variable, and a geom space expression
inductive geomSpaceCmd
| geomSpaceAssmt (v : geomSpaceVar) (e : GeometricSpaceExpression) : geomSpaceCmd

--time Space commands
inductive timeSpaceCmd
| timeSpaceAssmt (v : timeSpaceVar) (e : TimeSpaceExpression) : timeSpaceCmd

--Environments are similar to interpretations, assign values to variables
abbreviation geomSpaceEnvironment := (geomSpaceVar → geomSpace)
abbreviation timeSpaceEnvironment := (timeSpaceVar → timeSpace)

--Eval functions take in an expression, and an environment, and then returns a geomSpace
def geomSpaceEval : GeometricSpaceExpression → geomSpaceEnvironment → geomSpace 
| (GeometricSpaceExpression.GeometricSpaceLiteral V) E := V
| (GeometricSpaceExpression.GeometricSpaceVariable v) E := E v
| (GeometricSpaceExpression.GeometricSpaceFunctionApp V1 V2) E := V1 --not sure how to combine spaces yet

def timeSpaceEval : TimeSpaceExpression → timeSpaceEnvironment → timeSpace
| (TimeSpaceExpression.TimeSpaceLiteral V) E := V
| (TimeSpaceExpression.TimeSpaceVariable v) E := E v
| (TimeSpaceExpression.TimeSpaceFunctionApp V1 V2) E := V1

--default environments
def geomDefaultEnv : geomSpaceEnvironment := λ v, geomSpace.mk 3
def timeDefaultEnv : timeSpaceEnvironment := λ (v : timeSpaceVar), timeSpace.mk


--Command Eval functions take in a command, an environment, and returns a new updated environment
--after assigning the new value to the variable 
def GeomSpaceCmd_eval : geomSpaceCmd → geomSpaceEnvironment → geomSpaceEnvironment 
| (geomSpaceCmd.geomSpaceAssmt v e) E := 
    let var_num := v.num in 
    λ (var : geomSpaceVar),
        match var with
        | (geomSpaceVar.mk var_num) := geomSpaceEval e E
        end


def TimeSpaceCmd_eval : timeSpaceCmd → timeSpaceEnvironment → timeSpaceEnvironment 
| (timeSpaceCmd.timeSpaceAssmt v e) E :=
    let var_num := v.num in
    λ (var : timeSpaceVar),
        match var with
        | (timeSpaceVar.mk var_num) := timeSpaceEval e E
        end

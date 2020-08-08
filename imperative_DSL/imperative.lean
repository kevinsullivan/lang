--will import these later, temporary structures
inductive geomSpace : Type
| mk (dim : ℕ) : geomSpace

inductive timeSpace : Type
| mk

--variable types
structure geomSpaceVar : Type := 
mk :: (n : ℕ) 

structure timeSpaceVar : Type :=
mk :: (n : ℕ) 


inductive GeometricSpaceExpression
| GeometricSpaceLiteral (V : geomSpace) : GeometricSpaceExpression
| GeometricSpaceVariable (v : geomSpaceVar) : GeometricSpaceExpression
| GeometricSpaceFunctionApp (V1 V2 : geomSpace) : GeometricSpaceExpression

inductive TimeSpaceExpression
| TimeSpaceLiteral (V : timeSpace) : TimeSpaceExpression
| TimeSpaceVariable (v : timeSpaceVar) : TimeSpaceExpression
| TimeSpaceFunctionApp (V1 V2 : timeSpace) : TimeSpaceExpression


inductive geomSpaceCmd
| geomSpaceAssmt (v : geomSpaceVar) (e : GeometricSpaceExpression) : geomSpaceCmd

inductive timeSpaceCmd
| timeSpaceAssmt (v : timeSpaceVar) (e : TimeSpaceExpression) : timeSpaceCmd

abbreviation geomSpaceEnvironment := (geomSpaceVar → geomSpace)
abbreviation timeSpaceEnvironment := (timeSpaceVar → timeSpace)


def geomSpaceEval : GeometricSpaceExpression → geomSpaceEnvironment → geomSpace 
| (GeometricSpaceExpression.GeometricSpaceLiteral V) E := V
| (GeometricSpaceExpression.GeometricSpaceVariable v) E := E v
| (GeometricSpaceExpression.GeometricSpaceFunctionApp V1 V2) E := V1

def timeSpaceEval : TimeSpaceExpression → timeSpaceEnvironment → timeSpace
| (TimeSpaceExpression.TimeSpaceLiteral V) E := V
| (TimeSpaceExpression.TimeSpaceVariable v) E := E v
| (TimeSpaceExpression.TimeSpaceFunctionApp V1 V2) E := V1

def geomDefaultEnv : geomSpaceEnvironment := λ (v : geomSpaceVar), geomSpace.mk 3

def timeDefaultEnv : timeSpaceEnvironment := λ (v : timeSpaceVar), timeSpace.mk

def GeomSpaceCmd_eval : geomSpaceCmd → geomSpaceEnvironment 
| (geomSpaceCmd.geomSpaceAssmt v e) := 
    let var_num := v.n in 
    λ (var : geomSpaceVar),
        match var with
        | (geomSpaceVar.mk var_num) := geomSpaceEval e geomDefaultEnv
        end
        


def TimeSpaceCmd_eval : timeSpaceCmd → timeSpaceEnvironment 
| c := match c with
    | (timeSpaceCmd.timeSpaceAssmt v e) := 
        λ (var : timeSpaceVar),
            match var with
            | v := timeSpaceEval e timeDefaultEnv
            end
    end

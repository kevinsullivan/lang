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

def geomSpaceVarEq : geomSpaceVar → geomSpaceVar → bool
| v1 v2 := v1.num=v2.num

def timeSpaceVarEq : timeSpaceVar → timeSpaceVar → bool
| v1 v2 := v1.num=v2.num


--GeometricSpaceExpression
--Can be a literal, a variable, or function application expression
inductive GeometricSpaceExpression
| GeometricSpaceLiteral (V : geomSpace) : GeometricSpaceExpression
| GeometricSpaceVariable (v : geomSpaceVar) : GeometricSpaceExpression
| GeometricProduct (V1 V2 : geomSpace) : GeometricSpaceExpression

--Same for time spaces
inductive TimeSpaceExpression
| TimeSpaceLiteral (V : timeSpace) : TimeSpaceExpression
| TimeSpaceVariable (v : timeSpaceVar) : TimeSpaceExpression
-- | TimeSpaceFunctionApp (V1 V2 : timeSpace) : TimeSpaceExpression

--geometric Space Commands
--a geomSpaceAssmt takes in a geom space variable, and a geom space expression
inductive geomSpaceCmd
| geomSpaceAssmt (v : geomSpaceVar) (e : GeometricSpaceExpression) : geomSpaceCmd

--time Space commands
inductive timeSpaceCmd
| timeSpaceAssmt (v : timeSpaceVar) (e : TimeSpaceExpression) : timeSpaceCmd

--Environments are similar to interpretations, assign values to variables
def geomSpaceEnvironment := (geomSpaceVar → geomSpace)
def timeSpaceEnvironment := (timeSpaceVar → timeSpace)



--Eval functions take in an expression, and an environment, and then returns a geomSpace
def geomSpaceEval : GeometricSpaceExpression → geomSpaceEnvironment → geomSpace 
| (GeometricSpaceExpression.GeometricSpaceLiteral V) E := V
| (GeometricSpaceExpression.GeometricSpaceVariable v) E := E v
| (GeometricSpaceExpression.GeometricProduct V1 V2) E := V1 --not sure how to combine spaces yet

def timeSpaceEval : TimeSpaceExpression → timeSpaceEnvironment → timeSpace
| (TimeSpaceExpression.TimeSpaceLiteral V) E := V
| (TimeSpaceExpression.TimeSpaceVariable v) E := E v
--| (TimeSpaceExpression.TimeSpaceFunctionApp V1 V2) E := V1

--default environments
def geomDefaultEnv : geomSpaceEnvironment := λ v, geomSpace.mk 3
def timeDefaultEnv : timeSpaceEnvironment := λ (v : timeSpaceVar), timeSpace.mk


--Command Eval functions take in a command, an environment, and returns a new updated environment
--after assigning the new value to the variable 
def GeomSpaceCmd_eval : geomSpaceCmd → geomSpaceEnvironment → geomSpaceEnvironment 
| (geomSpaceCmd.geomSpaceAssmt v e) E :=  
    λ (var : geomSpaceVar),
        if (geomSpaceVarEq v var) then (geomSpaceEval e E) else (E var)


def TimeSpaceCmd_eval : timeSpaceCmd → timeSpaceEnvironment → timeSpaceEnvironment 
| (timeSpaceCmd.timeSpaceAssmt v e) E :=
    λ (var : timeSpaceVar),
        if (timeSpaceVarEq v var) then (timeSpaceEval e E) else (E var)

def my_var : geomSpaceVar := geomSpaceVar.mk 0

def myProgram : geomSpaceCmd := geomSpaceCmd.geomSpaceAssmt my_var (GeometricSpaceExpression.GeometricSpaceLiteral (geomSpace.mk 3))

#reduce GeomSpaceCmd_eval myProgram geomDefaultEnv
/- DEMO -/

inductive bvar : Type
| mk (n : ℕ)

def bvar_eq : bvar → bvar → bool
| (bvar.mk n1) (bvar.mk n2) := n1=n2

inductive bExpr : Type
|BLit (b: bool)
|BVar (v: bvar)

-- An environment is a function from bvar to bool

def benv := bvar → bool

def bEval : bExpr → benv → bool
| (bExpr.BLit b) i := b
| (bExpr.BVar v) i := i v


def init_benv : benv := λ v, ff

def update_benv : benv → bvar → bool → benv 
| e v b := λ v2, if (bvar_eq v v2) then b else (e v2)

inductive bCmd : Type
| bAssm (v : bvar) (e : bExpr)
| bSeq (c1 c2 : bCmd)

def cEval : benv → bCmd → benv 
| i0 c :=   match c with
            | (bCmd.bAssm v e) := update_benv i0 v (bEval e i0)
            | (bCmd.bSeq c1 c2) := 
                let i1 := (cEval i0 c1) in (cEval i1 c2)
            end

def myFirstProg := bCmd.bAssm (bvar.mk 0) (bExpr.BLit ff)

def newEnv := cEval init_benv myFirstProg

#eval newEnv (bvar.mk 0)
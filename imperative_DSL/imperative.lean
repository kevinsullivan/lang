import ..expressions.geometry
import ..expressions.time
import ...phys.src.space



/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/

/-
Variables
-/

-- equality

/-
Expressions
-/


/-
Commands
-/

--geometric Space Commands
--a classicalGeometryAssmt takes in a geom space variable, and a geom space expression
inductive classicalGeometryCmd
| classicalGeometryAssmt (v : classicalGeometryVar) (e : classicalGeometryExpression) : classicalGeometryCmd
| skip
| classicalGeometrySeq (c1 c2 : classicalGeometryCmd)
| classicalGeometryIf (b : bool) (c1 c2 : classicalGeometryCmd) --boolexpr!

--time Space commands
inductive classicalTimeCmd
| classicalTimeAssmt (v : classicalTimeVar) (e : classicalTimeExpression) : classicalTimeCmd
| skip
| classicalTimeSeq (c1 c2 : classicalTimeCmd)
| classicalTimeIf (b : bool) (c1 c2 : classicalTimeCmd)

--Environments are similar to interpretations, assign values to variables


--Eval functions take in an expression, and an environment, and then returns a classicalGeometry
def classicalTimeEval : classicalTimeExpression → classicalTimeEnvironment → Space.classicalTime
| (classicalTimeExpression.classicalTimeLiteral V) E := V
| (classicalTimeExpression.classicalTimeVariable v) E := E v
--| (classicalTimeExpression.classicalTimeFunctionApp V1 V2) E := V1

--default environments
def geomDefaultEnv : classicalGeometryEnvironment := λ v, Space.classicalGeometry.mk "world" 3
def timeDefaultEnv : classicalTimeEnvironment := λ v, Space.classicalTime.mk "world"


--Command Eval functions take in a command, an environment, and returns a new updated environment
--after assigning the new value to the variable 
def classicalGeometryCmd_eval : classicalGeometryCmd → classicalGeometryEnvironment → classicalGeometryEnvironment 
| (classicalGeometryCmd.classicalGeometryAssmt v e) E :=  
    λ (var : classicalGeometryVar),
        if (classicalGeometryVarEq v var) then (classicalGeometryEval e E) else (E var)
| (classicalGeometryCmd.skip) E := E
| (classicalGeometryCmd.classicalGeometrySeq c1 c2) E :=
    let i1 := classicalGeometryCmd_eval c1 E in 
        classicalGeometryCmd_eval c2 i1
| (classicalGeometryCmd.classicalGeometryIf b c1 c2) E := 
    if b then (classicalGeometryCmd_eval c1 E) else 
        (classicalGeometryCmd_eval c2 E)

def classicalTimeCmd_eval : classicalTimeCmd → classicalTimeEnvironment → classicalTimeEnvironment 
| (classicalTimeCmd.classicalTimeAssmt v e) E :=
    λ (var : classicalTimeVar),
        if (classicalTimeVarEq v var) then (classicalTimeEval e E) else (E var)
| (classicalTimeCmd.skip) E := E
| (classicalTimeCmd.classicalTimeSeq c1 c2) E :=
    let i1 := classicalTimeCmd_eval c1 E in 
        classicalTimeCmd_eval c2 i1
| (classicalTimeCmd.classicalTimeIf b c1 c2) E := 
    if b then (classicalTimeCmd_eval c1 E) else 
        (classicalTimeCmd_eval c2 E)


def my_var : classicalGeometryVar := classicalGeometryVar.mk 0

def myProgram : classicalGeometryCmd := classicalGeometryCmd.classicalGeometryAssmt my_var (classicalGeometryExpression.GeometricSpaceLiteral (Space.classicalGeometry.mk "" 3))

#eval classicalGeometryCmd_eval myProgram geomDefaultEnv
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
| bSkip
| bAssm (v : bvar) (e : bExpr)
| bSeq (c1 c2 : bCmd)
| bIf (b : bool) (c1 c2 : bCmd)

def cEval : benv → bCmd → benv 
| i0 c :=   match c with
            | bCmd.bSkip := i0
            | (bCmd.bAssm v e) := update_benv i0 v (bEval e i0)
            | (bCmd.bSeq c1 c2) := 
                begin
                    have i1 := cEval i0 c1,
                    have i2 := cEval i1 c2,
                    exact i0, -- exact i2,
                end
                -- let i1 := (cEval i0 c1) in
                --  (cEval i1 c2)
            | (bCmd.bIf b c1 c2) := match b with 
                | tt := i0 --cEval i0 c1
                | ff := i0 --cEval i0 c2
                end
            end

def myFirstProg := bCmd.bAssm (bvar.mk 0) (bExpr.BLit ff)

def newEnv := cEval init_benv myFirstProg

#eval newEnv (bvar.mk 0) 
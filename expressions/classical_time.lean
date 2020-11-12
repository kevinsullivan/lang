import ...phys.src.classical_time

namespace lang.classicalTime

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar extends var

def p : spaceVar := ⟨⟨1⟩⟩

inductive spaceExpr
| lit (v : classicalTime) 
| var (v : spaceVar)
abbreviation spaceEnv := spaceVar → classicalTime
abbreviation spaceEval := spaceExpr → spaceEnv → classicalTime


structure frameVar extends var
inductive frameExpr
| lit (f : classicalTimeFrame)
| var (v : frameVar) 
abbreviation frameEnv := frameVar → classicalTimeFrame
abbreviation frameEval := frameExpr → frameEnv → classicalTimeFrame


/-
structure frameVar (sp : spaceExpr) extends var
inductive frameExpr
| lit {t : classicalTime} (f : classicalTimeFrame t)
| var {sp : spaceExpr} (v : frameVar sp) 

abbreviation frameEnv_sp 
    (spe : spaceExpr) (eval : spaceEval) (env : spaceEnv) :=
    ∀fv : frameVar spe, 
        classicalTimeFrame (eval spe env)
abbreviation frameEnv (env : spaceEnv) 
    := 
        ∀eval : spaceEval,
        ∀spe : spaceExpr, 
        frameEnv_sp spe eval env
abbreviation frameEval (spe : spaceExpr) :=
    ∀fexpr : frameExpr, 
    ∀env : spaceEnv,
    ∀fe : frameEnv env,
    ∀eval : spaceEval,
        classicalTimeFrame (eval spe env)


--abbreviation

/-
structure vectorVar (sp : spaceExpr) extends var 
inductive vectorExpr
| lit {t : classicalTime} (f : classicalTimeCoordinateVector t)
| var {sp : spaceExpr} (v : vectorVar sp) 

abbreviation vectorEnv_sp 
    (spe : spaceExpr) (eval : spaceEval) (env : spaceEnv) :=
    ∀fv : vectorVar spe, 
        classicalTimeCoordinateVector (eval spe env)
abbreviation vectorEnv (env : spaceEnv) 
    := 
        ∀eval : spaceEval,
        ∀spe : spaceExpr, 
        vectorEnv_sp spe eval env
abbreviation vectorEval (spe : spaceExpr) :=
    ∀fexpr : vectorExpr, 
    ∀env : spaceEnv,
    ∀fe : vectorEnv env,
    ∀eval : spaceEval,
        classicalTimeCoordinateVector (eval spe env)


structure pointVar (sp : spaceExpr) extends var
inductive pointExpr
| lit {t : classicalTime} (f : classicalTimeCoordinateVector t)
| var {sp : spaceExpr} (v : vectorVar sp) 

abbreviation pointEnv_sp 
    (spe : spaceExpr) (eval : spaceEval) (env : spaceEnv) :=
    ∀p : pointVar spe, 
        classicalTimeCoordinatePoint (eval spe env)
abbreviation pointEnv (env : spaceEnv) 
    := 
        ∀eval : spaceEval,
        ∀spe : spaceExpr, 
        pointEnv_sp spe eval env
abbreviation pointEval (spe : spaceExpr) :=
    ∀fexpr : pointExpr, 
    ∀env : spaceEnv,
    ∀fe : pointEnv env,
    ∀eval : spaceEval,
        classicalTimeCoordinatePoint (eval spe env)
-/-/

def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
/-def vectorVarEq {sp : spaceExpr} : vectorVar sp → vectorVar sp → bool
| v1 v2 := v1.num=v2.num
def pointVarEq {sp : spaceExpr} : pointVar sp → pointVar sp → bool
| v1 v2 := v1.num=v2.num-/
def frameVarEq : frameVar → frameVar → bool
| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(fr : frameEnv)
--(vec : vectorEnv sp)
--(pt : pointEnv sp)



noncomputable def initSp := λ v : spaceVar, worldTime
noncomputable def initFr := λ v : frameVar, classicalTime.stdFrame worldTime


end lang.classicalTime
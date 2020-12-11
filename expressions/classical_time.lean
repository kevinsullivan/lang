import ...phys.src.classical_time

namespace lang.classicalTime

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar extends var

def myvar : spaceVar := ⟨⟨2⟩⟩

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

structure ScalarVar extends var
inductive ScalarExpr
| lit (f : classicalTimeScalar)
| var (v : ScalarVar) 
abbreviation scalarEnv := ScalarVar → classicalTimeScalar
abbreviation scalarEval := ScalarExpr → scalarEnv → classicalTimeScalar


--abbreviation


structure CoordinateVectorVar extends var 
inductive CoordinateVectorExpr
| lit (f : classicalTimeCoordinateVector)
| var (v : CoordinateVectorVar) 
abbreviation CoordinateVectorEnv := CoordinateVectorVar → classicalTimeCoordinateVector
abbreviation CoordinateVectorEval := CoordinateVectorExpr → CoordinateVectorEnv → classicalTimeCoordinateVector

structure CoordinatePointVar extends var
inductive CoordinatePointExpr
| lit (f : classicalTimeCoordinatePoint)
| var(v : CoordinatePointVar ) 
abbreviation pointEnv := CoordinatePointVar → classicalTimeCoordinatePoint
abbreviation pointEval := CoordinatePointExpr → pointEnv → classicalTimeCoordinatePoint

def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
def CoordinateVectorVarEq : CoordinateVectorVar → CoordinateVectorVar → bool
| v1 v2 := v1.num=v2.num
def pointVarEq : CoordinatePointVar → CoordinatePointVar → bool
| v1 v2 := v1.num=v2.num
def frameVarEq : frameVar → frameVar → bool
| v1 v2 := v1.num=v2.num
def scalarVarEq : ScalarVar → ScalarVar → bool
| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(fr : frameEnv )
(vec : CoordinateVectorEnv)
(pt : pointEnv)
(s : scalarEnv)



noncomputable def initSp := λ v : spaceVar, classicalTime.build 9999
noncomputable def initFr := 
    λ v : frameVar, 
        classicalTime.stdFrame (initSp ⟨⟨9999⟩⟩)
noncomputable def initVec := 
    λ v : CoordinateVectorVar, 
        classicalTimeCoordinateVector.build (initSp ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩) ⟨[1], by refl⟩
noncomputable def initPt := 
    λ v : CoordinatePointVar, 
        classicalTimeCoordinatePoint.build (initSp ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩) ⟨[1], by refl⟩
noncomputable def initScalar := 
    λ v : ScalarVar, 
        classicalTimeScalar.build (initSp ⟨⟨9999⟩⟩) ⟨[1],rfl⟩
noncomputable def 
    initEnv : env := 
        ⟨initSp, initFr, initVec, initPt, initScalar⟩

end lang.classicalTime
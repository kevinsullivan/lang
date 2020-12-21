import ...phys.src.classical_geometry

namespace lang.euclideanGeometry3

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar extends var

def myvar : spaceVar := ⟨⟨2⟩⟩

def p : spaceVar := ⟨⟨1⟩⟩

inductive spaceExpr
| lit (v : euclideanGeometry3) 
| var (v : spaceVar)
abbreviation spaceEnv := spaceVar → euclideanGeometry3
abbreviation spaceEval := spaceExpr → spaceEnv → euclideanGeometry3

structure frameVar extends var
inductive frameExpr
| lit (f : euclideanGeometry3Frame)
| var (v : frameVar) 
abbreviation frameEnv := frameVar → euclideanGeometry3Frame
abbreviation frameEval := frameExpr → frameEnv → euclideanGeometry3Frame

structure TransformVar extends var
inductive TransformExpr
| lit (t : euclideanGeometry3Transform)
| var (v : TransformVar)
abbreviation transformEnv := TransformVar → euclideanGeometry3Transform
abbreviation transformEval := TransformExpr → transformEnv → euclideanGeometry3Transform


structure ScalarVar extends var
inductive ScalarExpr
| lit (f : euclideanGeometry3Scalar)
| var (v : ScalarVar) 
abbreviation scalarEnv := ScalarVar → euclideanGeometry3Scalar
abbreviation scalarEval := ScalarExpr → scalarEnv → euclideanGeometry3Scalar


--abbreviation


structure CoordinateVectorVar extends var 
inductive CoordinateVectorExpr
| lit (f : euclideanGeometry3CoordinateVector)
| var (v : CoordinateVectorVar) 
abbreviation CoordinateVectorEnv := CoordinateVectorVar → euclideanGeometry3CoordinateVector
abbreviation CoordinateVectorEval := CoordinateVectorExpr → CoordinateVectorEnv → euclideanGeometry3CoordinateVector

structure CoordinatePointVar extends var
inductive CoordinatePointExpr
| lit (f : euclideanGeometry3CoordinatePoint)
| var(v : CoordinatePointVar ) 
abbreviation pointEnv := CoordinatePointVar → euclideanGeometry3CoordinatePoint
abbreviation pointEval := CoordinatePointExpr → pointEnv → euclideanGeometry3CoordinatePoint

def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
def vectorVarEq : CoordinateVectorVar → CoordinateVectorVar → bool
| v1 v2 := v1.num=v2.num
def pointVarEq : CoordinatePointVar → CoordinatePointVar → bool
| v1 v2 := v1.num=v2.num
def frameVarEq : frameVar → frameVar → bool
| v1 v2 := v1.num=v2.num
def transformVarEq : TransformVar → TransformVar → bool
| v1 v2 := v1.num=v2.num
def scalarVarEq : ScalarVar → ScalarVar → bool
| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(fr : frameEnv )
(tr : transformEnv)
(vec : CoordinateVectorEnv)
(pt : pointEnv)
(s : scalarEnv)



noncomputable def initSp := λ v : spaceVar, euclideanGeometry3.build 9999
noncomputable def initFr := 
    λ v : frameVar, 
        euclideanGeometry3.stdFrame (initSp ⟨⟨9999⟩⟩)
noncomputable def initTransform :=
    λ v : TransformVar,
        euclideanGeometry3Transform.mk (initSp ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩)
noncomputable def initVec := 
    λ v : CoordinateVectorVar, 
        euclideanGeometry3CoordinateVector.build (initSp ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩) ⟨[1,1,1], by refl⟩
noncomputable def initPt := 
    λ v : CoordinatePointVar, 
        euclideanGeometry3CoordinatePoint.build (initSp ⟨⟨9999⟩⟩) (initFr ⟨⟨9999⟩⟩) ⟨[1,1,1], by refl⟩
noncomputable def initScalar := 
    λ v : ScalarVar, 
        euclideanGeometry3Scalar.build (initSp ⟨⟨9999⟩⟩) ⟨[1],rfl⟩
noncomputable def 
    initEnv : env := 
        ⟨initSp, initFr, initTransform, initVec, initPt, initScalar⟩

end lang.euclideanGeometry3
import ...phys.src.classical_geometry

namespace lang.euclideanGeometry

open measurementSystem

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar (n : ℕ) extends var

inductive spaceExpr (n : ℕ)
| lit (v : euclideanGeometry n) : spaceExpr
| var (v : spaceVar n) : spaceExpr
abbreviation spaceEnv := 
    Πn : ℕ,
    spaceVar n → euclideanGeometry n
abbreviation spaceEval := 
    Σn : ℕ, 
    spaceExpr n → spaceEnv → euclideanGeometry n

structure frameVar (sig : Σn:ℕ, euclideanGeometry n) extends var
inductive frameExpr (sig : Σn:ℕ, euclideanGeometry n) --n : ℕ} (sp : euclideanGeometry n)
| lit (f : euclideanGeometryFrame sig.2) : frameExpr
| var (v : frameVar sig) : frameExpr
abbreviation frameEnv := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    frameVar sig → euclideanGeometryFrame sig.2
abbreviation frameEval := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    --Πn : ℕ,
    --Πsp : euclideanGeometry n,
    frameExpr sig → frameEnv → euclideanGeometryFrame sig.2

#check (ℕ,ℕ)

structure TransformVar 
    (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s))
                --{n : ℕ} {sp : euclideanGeometry n} (from_ : euclideanGeometryFrame sp) (to_ : euclideanGeometryFrame sp) 
    extends var
inductive TransformExpr 
    (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s))
                
                --{n : ℕ} {sp : euclideanGeometry n} (from_ : euclideanGeometryFrame sp) (to_ : euclideanGeometryFrame sp)
| lit (t : euclideanGeometryTransform sig.2.2.1 sig.2.2.2) : TransformExpr
| var (v : TransformVar sig) : TransformExpr
abbreviation transformEnv :=
    Π(sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s)),
    TransformVar sig → euclideanGeometryTransform sig.2.2.1 sig.2.2.2
abbreviation transformEval := 
    Π(sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s)),
    TransformExpr sig → transformEnv → euclideanGeometryTransform sig.2.2.1 sig.2.2.2


structure QuantityVar --{n : ℕ} (sp : euclideanGeometry n) (m : measurementSystem.MeasurementSystem) 
    (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem)
    extends var
inductive QuantityExpr (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem)--{n : ℕ} (sp : euclideanGeometry n) (m : measurementSystem.MeasurementSystem)
| lit (f : euclideanGeometryQuantity sig.2.1 sig.2.2) : QuantityExpr
| var (v : QuantityVar sig) : QuantityExpr
abbreviation QuantityEnv := 
    Π(sig : Σn, Σs: euclideanGeometry n,MeasurementSystem),
    --Πn : ℕ,
    --Πsp : euclideanGeometry n,
    --Πm : MeasurementSystem,
    QuantityVar sig → euclideanGeometryQuantity sig.2.1 sig.2.2
abbreviation QuantityEval := 
    Π(sig : Σn, Σs: euclideanGeometry n,MeasurementSystem),
    --Πn : ℕ,
    --Πsp : euclideanGeometry n,
    --Πm : MeasurementSystem,
    QuantityExpr sig → QuantityEnv → euclideanGeometryQuantity sig.2.1 sig.2.2

structure AngleVar (sig : Σn:ℕ, euclideanGeometry n) extends var
inductive AngleExpr (sig : Σn:ℕ, euclideanGeometry n)
| lit (a : euclideanGeometryAngle sig.2) : AngleExpr
| var (v : AngleVar sig) : AngleExpr

abbreviation AngleEnv := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    AngleVar sig → euclideanGeometryAngle sig.2
abbreviation AngleEval := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    AngleExpr sig → AngleEnv → euclideanGeometryAngle sig.2


--abbreviation


structure CoordinateVectorVar --{n : ℕ} {sp : euclideanGeometry n} (fr : euclideanGeometryFrame sp) 
    (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)
    extends var 
inductive CoordinateVectorExpr (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)--{n : ℕ} {sp : euclideanGeometry n} (fr : euclideanGeometryFrame sp)
| lit (v : euclideanGeometryCoordinateVector sig.2.2) : CoordinateVectorExpr
| var (v : CoordinateVectorVar sig) : CoordinateVectorExpr

abbreviation CoordinateVectorEnv := 
    Π(sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    --Πn : ℕ,
    --Πsp : euclideanGeometry n,
    --Πfr : euclideanGeometryFrame sp,
    CoordinateVectorVar sig → euclideanGeometryCoordinateVector sig.2.2

abbreviation CoordinateVectorEval :=
    Π(sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    --Πn : ℕ,
    --Πsp : euclideanGeometry n,
    --Πfr : euclideanGeometryFrame sp,
    CoordinateVectorExpr sig → CoordinateVectorEnv → euclideanGeometryCoordinateVector sig.2.2


structure CoordinatePointVar (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)--{n : ℕ} {sp : euclideanGeometry n} (fr : euclideanGeometryFrame sp) 
    extends var 
inductive CoordinatePointExpr (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s)--{n : ℕ} {sp : euclideanGeometry n} (fr : euclideanGeometryFrame sp)
| lit (v : euclideanGeometryCoordinatePoint sig.2.2) : CoordinatePointExpr
| var (v : CoordinatePointVar sig) : CoordinatePointExpr 

abbreviation CoordinatePointEnv := 
    Π(sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    CoordinatePointVar sig → euclideanGeometryCoordinatePoint sig.2.2
abbreviation CoordinatePointEval := 
    Π(sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    CoordinatePointExpr sig → CoordinatePointEnv → euclideanGeometryCoordinatePoint sig.2.2

structure OrientationVar (sig : Σn:ℕ, euclideanGeometry n) extends var
inductive OrientationExpr (sig : Σn:ℕ, euclideanGeometry n)
| lit (f : euclideanGeometryOrientation sig.2) : OrientationExpr
| var (v : OrientationVar sig) : OrientationExpr

abbreviation OrientationEnv :=
    Π(sig : Σn:ℕ, euclideanGeometry n), 
    OrientationVar sig → euclideanGeometryOrientation sig.2
abbreviation OrientationEval := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    OrientationExpr sig → OrientationEnv → euclideanGeometryOrientation sig.2


structure RotationVar (sig : Σn:ℕ, euclideanGeometry n)--{n : ℕ} (sp : euclideanGeometry n) 
    extends var
inductive RotationExpr (sig : Σn:ℕ, euclideanGeometry n)--{n : ℕ} (sp : euclideanGeometry n)
| lit (f : euclideanGeometryRotation sig.2) : RotationExpr
| var (v : RotationVar sig) : RotationExpr

abbreviation RotationEnv := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    RotationVar sig → euclideanGeometryRotation sig.2

abbreviation RotationEval := 
    Π(sig : Σn:ℕ, euclideanGeometry n),
    RotationExpr sig → RotationEnv → euclideanGeometryRotation sig.2


--def spaceVarEq {n1 : ℕ} {n2 : ℕ}: spaceVar n1 → spaceVar n2 → bool
--| v1 v2 := v1.num=v2.num∧n1=n2
--def vectorVarEq {n : ℕ} {sp : euclideanGeometry n} {fr : euclideanGeometryFrame sp }
--    : CoordinateVectorVar fr → CoordinateVectorVar fr → bool
--| v1 v2 := v1.num=v2.num
--def pointVarEq {n : ℕ} {sp : euclideanGeometry n} {fr : euclideanGeometryFrame sp }
--    : CoordinatePointVar fr → CoordinatePointVar fr → bool
--| v1 v2 := v1.num=v2.num
--def frameVarEq {n : ℕ} {sp : euclideanGeometry n}: frameVar sp → frameVar sp → bool
--| v1 v2 := v1.num=v2.num
--def transformVarEq {n : ℕ} {sp : euclideanGeometry n} {from_ : euclideanGeometryFrame sp } {to_ : euclideanGeometryFrame sp }: TransformVar from_ to_ → TransformVar from_ to_ → bool
--| v1 v2 := v1.num=v2.num
--def QuantityVarEq {n : ℕ} {sp : euclideanGeometry n} {m : MeasurementSystem}: QuantityVar sp m → QuantityVar sp m → bool
--| v1 v2 := v1.num=v2.num
--def angleVarEq {n : ℕ} {sp : euclideanGeometry n}: AngleVar sp → AngleVar sp → bool
--| v1 v2 := v1.num=v2.num
--def orientationVarEq {n : ℕ} {sp : euclideanGeometry n}: OrientationVar sp → OrientationVar sp → bool
--| v1 v2 := v1.num=v2.num
--def rotationVarEq {n : ℕ} {sp : euclideanGeometry n}: RotationVar sp → RotationVar sp → bool
--| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(fr : frameEnv )
(tr : transformEnv)
(vec : CoordinateVectorEnv)
(pt : CoordinatePointEnv)
(q : QuantityEnv)
(a : AngleEnv)
(or : OrientationEnv)
(r : RotationEnv)


noncomputable def initSp : spaceEnv :=
    --λ n : ℕ,
    --λ v : spaceVar n,
    λ (n : ℕ),
    λ v : spaceVar n,
    (euclideanGeometry.build n 9999)
def initFr : frameEnv :=
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    --λ v : frameVar sp, 
    λ (sig : Σn:ℕ, euclideanGeometry n),
    λ v : frameVar sig,
        sig.2.stdFrame
noncomputable def initTransform : transformEnv :=
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    --λ from_ : euclideanGeometryFrame sp,
    --λ to_ : euclideanGeometryFrame sp,
    λ (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s)),
    λ v : TransformVar sig,
        euclideanGeometryTransform.build sig.snd.snd.fst sig.snd.snd.snd
noncomputable def initVec : CoordinateVectorEnv := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    --λ fr : euclideanGeometryFrame sp,
    λ (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    λ v : CoordinateVectorVar sig, 
        euclideanGeometryCoordinateVector.build sig.2.2 ⟨list.repeat 1 sig.1, sorry⟩
def initPt : CoordinatePointEnv := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    --λ fr : euclideanGeometryFrame sp,
    λ (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s),
    λ v : CoordinatePointVar sig, 
        euclideanGeometryCoordinatePoint.build sig.2.2 ⟨list.repeat 1 sig.1, sorry⟩
def initQuantity : QuantityEnv := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    --λ m : MeasurementSystem,
    λ (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem),
    λ v : QuantityVar sig, 
        euclideanGeometryQuantity.build sig.2.1 sig.2.2  ⟨[1],rfl⟩
def initAngle : AngleEnv := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    λ (sig : Σn:ℕ, euclideanGeometry n),
    λ v : AngleVar sig, 
        euclideanGeometryAngle.build sig.2 ⟨[1],rfl⟩
noncomputable def initOrientation : OrientationEnv := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    λ (sig : Σn:ℕ, euclideanGeometry n),
    λ v : OrientationVar sig, 
        euclideanGeometryOrientation.build sig.2 ⟨list.repeat ⟨list.repeat 1 sig.1, sorry⟩ sig.1, sorry⟩
noncomputable def initRotation := 
    --λ n : ℕ,
    --λ sp : euclideanGeometry n,
    λ (sig : Σn:ℕ, euclideanGeometry n),
    λ v : RotationVar sig, 
        euclideanGeometryRotation.build sig.2 ⟨list.repeat ⟨list.repeat 1 sig.1, sorry⟩ sig.1, sorry⟩
noncomputable def 
    initEnv : env := 
        ⟨initSp, initFr, initTransform, initVec, initPt, initQuantity, initAngle, initOrientation, initRotation⟩

end lang.euclideanGeometry
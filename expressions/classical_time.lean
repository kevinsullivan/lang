import ...phys.src.classical_time
import .expression

namespace lang.classicalTime

open measurementSystem

structure spaceVar extends var

inductive spaceExpr
| lit (v : classicalTime) 
| var (v : spaceVar)
abbreviation spaceEnv := spaceVar → classicalTime
abbreviation spaceEval := spaceExpr → spaceEnv → classicalTime

structure frameVar (sp : classicalTime) extends var
inductive frameExpr(sp : classicalTime)
| lit-- {sp : classicalTime } 
    (f : classicalTimeFrame sp) 
    : frameExpr
| var-- {sp : classicalTime } 
    (v : frameVar sp) 
    : frameExpr
abbreviation frameEnv := Πsp : classicalTime, frameVar sp → classicalTimeFrame sp
abbreviation frameEval := Πsp : classicalTime, frameExpr sp → frameEnv → classicalTimeFrame sp

structure TransformVar 
    --{sp : classicalTime } (from_ : classicalTimeFrame sp) (to_ : classicalTimeFrame sp) 
    (sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s)
    extends var
inductive TransformExpr
    (sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s)
| lit --{sp : classicalTime } {from_ : classicalTimeFrame sp} {to_ : classicalTimeFrame sp} 
    (t : classicalTimeTransform sig.2.1 sig.2.2) : TransformExpr
| var --{sp : classicalTime } {from_ : classicalTimeFrame sp} {to_ : classicalTimeFrame sp} 
    (v : TransformVar sig) : TransformExpr
abbreviation TransformEnv :=  
    Πsig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s,
    --Πsp : classicalTime, Πfrom_: classicalTimeFrame sp, Πto_: classicalTimeFrame sp, 
        TransformVar sig → classicalTimeTransform sig.2.1 sig.2.2
abbreviation TransformEval := 
    Πsig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s,
    --Πsp : classicalTime, Πfrom_: classicalTimeFrame sp, Πto_: classicalTimeFrame sp, 
        TransformExpr sig → TransformEnv → classicalTimeTransform sig.2.1 sig.2.2



structure QuantityVar --(sp : classicalTime) (m : measurementSystem.MeasurementSystem) 
    (sig: Σs : classicalTime, MeasurementSystem)
    extends var
inductive QuantityExpr (sig: Σs : classicalTime, MeasurementSystem)
| lit --{sp : classicalTime } {m : measurementSystem.MeasurementSystem} 
    (f : classicalTimeQuantity sig.1 sig.2) : QuantityExpr
| var --{sp : classicalTime} {m : measurementSystem.MeasurementSystem} 
    (v : QuantityVar sig) : QuantityExpr 
abbreviation QuantityEnv := 
    Π(sig: Σs : classicalTime, MeasurementSystem),--sp : classicalTime, Πm : measurementSystem.MeasurementSystem,
        QuantityVar sig → classicalTimeQuantity sig.1 sig.2
abbreviation QuantityEval := 
    Π(sig: Σs : classicalTime, MeasurementSystem),--sp : classicalTime, Πm : measurementSystem.MeasurementSystem,
        QuantityExpr sig → QuantityEnv → classicalTimeQuantity sig.1 sig.2


--abbreviation


structure CoordinateVectorVar --{sp : classicalTime } (fr : classicalTimeFrame sp) 
    (sig: Σs : classicalTime, classicalTimeFrame s)
    extends var 
inductive CoordinateVectorExpr
    (sig: Σs : classicalTime, classicalTimeFrame s)
| lit --{sp : classicalTime } {fr : classicalTimeFrame sp} 
    (f : classicalTimeCoordinateVector sig.2) : CoordinateVectorExpr
| var --{sp : classicalTime } {fr : classicalTimeFrame sp} 
    (v : CoordinateVectorVar sig) : CoordinateVectorExpr
abbreviation CoordinateVectorEnv := 
    Π(sig: Σs : classicalTime, classicalTimeFrame s),--sp : classicalTime, Πfr : classicalTimeFrame sp,
        CoordinateVectorVar sig → classicalTimeCoordinateVector sig.2
abbreviation CoordinateVectorEval := 
    Π(sig: Σs : classicalTime, classicalTimeFrame s),--sp : classicalTime, Πfr : classicalTimeFrame sp,
        CoordinateVectorExpr sig → CoordinateVectorEnv → classicalTimeCoordinateVector sig.2

structure CoordinatePointVar --{sp : classicalTime } (fr : classicalTimeFrame sp) 
    (sig: Σs : classicalTime, classicalTimeFrame s)
    extends var
inductive CoordinatePointExpr 
    (sig: Σs : classicalTime, classicalTimeFrame s)
| lit --{sp : classicalTime } {fr : classicalTimeFrame sp} 
    (p : classicalTimeCoordinatePoint sig.2) : CoordinatePointExpr 
| var --{sp : classicalTime } {fr : classicalTimeFrame sp} 
    (v : CoordinatePointVar sig) : CoordinatePointExpr 

abbreviation CoordinatePointEnv := 
    Π(sig: Σs : classicalTime, classicalTimeFrame s),--sp : classicalTime, Πfr : classicalTimeFrame sp,
        CoordinatePointVar sig → classicalTimeCoordinatePoint sig.2
abbreviation CoordinatePointEval := 
    Π(sig: Σs : classicalTime, classicalTimeFrame s),--sp : classicalTime, Πfr : classicalTimeFrame sp,
        CoordinatePointExpr sig → CoordinatePointEnv → classicalTimeCoordinatePoint sig.2
/-
def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
def CoordinateVectorVarEq {sp : classicalTime } {fr : classicalTimeFrame sp} : CoordinateVectorVar fr → CoordinateVectorVar fr → bool
| v1 v2 := v1.num=v2.num
def pointVarEq {sp : classicalTime } {fr : classicalTimeFrame sp} : CoordinatePointVar fr → CoordinatePointVar fr → bool
| v1 v2 := v1.num=v2.num
def frameVarEq {sp : classicalTime } : frameVar sp → frameVar sp → bool
| v1 v2 := v1.num=v2.num
def transformVarEq {sp : classicalTime } {from_ : classicalTimeFrame sp} {to_ : classicalTimeFrame sp} : transformVar from_ to_ → transformVar from_ to_ → bool
| v1 v2 := v1.num=v2.num
def QuantityVarEq {sp : classicalTime } {m : measurementSystem.MeasurementSystem} : QuantityVar sp m → QuantityVar sp m → bool
| v1 v2 := v1.num=v2.num
-/
structure env : Type :=
(sp : spaceEnv)
(fr : frameEnv )
(tr : TransformEnv)
(vec : CoordinateVectorEnv)
(pt : CoordinatePointEnv)
(q : QuantityEnv)



noncomputable def initSp : spaceEnv := λ v : spaceVar, classicalTime.build 9999
noncomputable def initFr : frameEnv := 
    λ sp : classicalTime,
    λ v : frameVar sp, 
        sp.stdFrame
noncomputable def initVec : CoordinateVectorEnv := 
   -- λ sp : classicalTime,
   -- λ fr : classicalTimeFrame sp,
    λ(sig: Σs : classicalTime, classicalTimeFrame s),
    λv : CoordinateVectorVar sig, 
        classicalTimeCoordinateVector.build sig.2 ⟨[1], by refl⟩

noncomputable def initPt : CoordinatePointEnv := 
    --λ sp : classicalTime,
    --λ fr : classicalTimeFrame sp,
    λ(sig: Σs : classicalTime, classicalTimeFrame s),
    λ v : CoordinatePointVar sig, 
        classicalTimeCoordinatePoint.build sig.2 ⟨[1], by refl⟩

noncomputable def initQuantity : QuantityEnv := 
    --λ sp : classicalTime,
    --λ m : measurementSystem.MeasurementSystem,
    λ (sig: Σs : classicalTime, MeasurementSystem),
    λ v : QuantityVar sig, 
        classicalTimeQuantity.build sig.1 sig.2 ⟨[1],rfl⟩

noncomputable def initTransform : TransformEnv :=
   -- λ sp : classicalTime,
    --λ from_ : classicalTimeFrame sp,
    --λ to_ : classicalTimeFrame sp,
    λ sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s,
    λ v : TransformVar sig,
        classicalTimeTransform.build sig.2.1 sig.2.2

noncomputable def 
    initEnv : env := 
        ⟨initSp, initFr, initTransform, initVec, initPt, initQuantity⟩

end lang.classicalTime
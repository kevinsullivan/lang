import ..imperative_DSL.environment
import ..eval.geometryEval

open lang.euclideanGeometry

open classical
local attribute [instance] prop_decidable --makes everything noncomputable which is problematic


open measurementSystem


noncomputable def assignGeometry3Space (n : ℕ)
  : environment.env → lang.euclideanGeometry.spaceVar n → spaceExpr n → environment.env
| i v e :=
  {
    g:={sp :=
                λ n1,
                λ r,
                let d := (i.g.sp n1 r) in
                if r.num = v.num then 
                  if eqn:n = n1 then
                    (euclideanGeometryEval (eq.rec e eqn) i)
                  else d 
                else d
                ..i.g},
    ..i
  }

noncomputable def assignGeometry3Frame  (sig : Σn:ℕ, euclideanGeometry n)
  : environment.env → lang.euclideanGeometry.frameVar sig → lang.euclideanGeometry.frameExpr sig → environment.env
| i v e := 
  {
    g:={fr := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryFrame sig1.snd := (i.g.fr sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : frameExpr sig1 := eq.rec e eqn in
                (euclideanGeometryFrameEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }

noncomputable def assignGeometry3Transform 
  (sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s))
  : environment.env → lang.euclideanGeometry.TransformVar sig → 
    lang.euclideanGeometry.TransformExpr sig → environment.env
| i v e := 
  {
    g:={tr := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryTransform sig1.2.2.1 sig1.2.2.2 := (i.g.tr sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : TransformExpr sig1 := eq.rec e eqn in
                (euclideanGeometryTransformEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }

noncomputable def assignGeometry3Vector
    (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s) :
      environment.env → lang.euclideanGeometry.CoordinateVectorVar sig → 
        lang.euclideanGeometry.CoordinateVectorExpr sig → environment.env 
| i v e := 
  {
    g:={vec := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryCoordinateVector sig1.2.2 := (i.g.vec sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : CoordinateVectorExpr sig1 := eq.rec e eqn in
                (euclideanGeometryCoordinateVectorEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }

noncomputable def assignGeometry3Point 
    (sig : Σn:ℕ, Σs:euclideanGeometry n,euclideanGeometryFrame s) :
      environment.env → lang.euclideanGeometry.CoordinatePointVar sig → 
        lang.euclideanGeometry.CoordinatePointExpr sig → environment.env 
| i v e := 
  {
    g:={pt := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryCoordinatePoint sig1.2.2 := (i.g.pt sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : CoordinatePointExpr sig1 := eq.rec e eqn in
                (euclideanGeometryCoordinatePointEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }

noncomputable def assignGeometry3Quantity 
    (sig : Σn, Σs: euclideanGeometry n,MeasurementSystem) : 
      environment.env → 
  lang.euclideanGeometry.QuantityVar sig → 
  lang.euclideanGeometry.QuantityExpr sig → environment.env 
| i v e := 
  {
    g:={q := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryQuantity sig1.2.1 sig1.2.2 := (i.g.q sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : QuantityExpr sig1 := eq.rec e eqn in
                (euclideanGeometryQuantityEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }
                

noncomputable def assignGeometry3Angle 
  (sig : Σn:ℕ, euclideanGeometry n) : environment.env → 
  lang.euclideanGeometry.AngleVar sig → 
  lang.euclideanGeometry.AngleExpr sig → environment.env 
| i v e := 
  {
    g:={a := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryAngle sig1.snd := (i.g.a sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : AngleExpr sig1 := eq.rec e eqn in
                (euclideanGeometryAngleEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }
                

noncomputable def assignGeometry3Orientation
  (sig : Σn:ℕ, euclideanGeometry n) : environment.env → 
  lang.euclideanGeometry.OrientationVar sig → 
  lang.euclideanGeometry.OrientationExpr sig → environment.env 
| i v e := 
  {
    g:={or := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryOrientation sig1.snd := (i.g.or sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : OrientationExpr sig1 := eq.rec e eqn in
                (euclideanGeometryOrientationEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }
                

noncomputable def assignGeometry3Rotation
  (sig : Σn:ℕ, euclideanGeometry n) : environment.env → 
  lang.euclideanGeometry.RotationVar sig → 
  lang.euclideanGeometry.RotationExpr sig → environment.env 
| i v e := 
  {
    g:={r := 
          λ sig1,
          λ v1,
            let d : euclideanGeometryRotation sig1.snd := (i.g.r sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : RotationExpr sig1 := eq.rec e eqn in
                (euclideanGeometryRotationEval sig1 e1 i)
              else d
            else d,
            ..i.g},
    ..i
  }
import ..imperative_DSL.environment
import ..eval.geometryEval

open lang.euclideanGeometry


open measurementSystem


def assignGeometrySpace (n : ℕ)
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

--constants (sig : Σn:ℕ, euclideanGeometry n) (sig1 : Σn1:ℕ, --euclideanGeometry n1)

def geo1 : euclideanGeometry 1 := euclideanGeometry.build 1 1
def geo2 : euclideanGeometry 1 := euclideanGeometry.build 1 1

instance eucl_eq 
  {n: ℕ}
  {sp : euclideanGeometry n}
  {sp1 : euclideanGeometry n}
  : decidable (sp=sp1) :=
  if n_eq : sp.id=sp1.id then 
    begin
      let t : sp = sp1 := begin
        induction sp,
        induction sp1,
        let : sp=sp1 := by cc,
        cc
      end,
      exact decidable.is_true t
    end  
  else
    begin
      let f : ¬(sp=sp1) := begin
        
        induction sp,
        induction sp1,
        let nsp : ¬(sp=sp1) := by cc,
        --by cc,
        simp *,
      end,
      exact decidable.is_false f
    end  


#eval (geo1=geo2:bool)
#check geo1==geo2

#check eq_rec_heq

#check heq.trans

instance  sig_fr_eq
  {sig : Σn:ℕ, euclideanGeometry n}
  {sig1 : Σn1:ℕ, euclideanGeometry n1}
  : decidable (sig=sig1)  := 
  if n_eq:sig.fst=sig1.fst then
    if id_eq:sig.snd.id=sig1.snd.id then 
      let recd : euclideanGeometry sig1.fst := n_eq.rec_on sig.snd in
      if sp_eq:sig1.snd=(n_eq.rec_on sig.snd) then
      begin
      let seq : sig = sig1 := 
        begin
          let tt : n_eq.rec_on sig.2 == sig.2 :=  (eq_rec_heq n_eq sig.2) ,
          let t3 : sig1.2 = (n_eq.rec_on sig.2) := by simp *,
          induction sig,
          induction sig1,
          simp *,
          cc,
        end,
      exact decidable.is_true seq
    end
      else 
        begin--spaces are not equal
          let sneq : ¬sig=sig1 := begin
           assume seq:sig=sig1,
            let h : ¬sig1.2 = (n_eq.rec_on sig.2) := by cc,
            let : sig1.2 = (n_eq.rec_on sig.2) := begin
              simp [seq],
              cc
            end,
            contradiction
          end,
          exact decidable.is_false sneq
        end
    else 
      begin -- id's are not equal
          let sneq : ¬sig=sig1 := begin
           assume seq:sig=sig1,
            let h : ¬sig1.2 = (n_eq.rec_on sig.2) := by cc,
            let : sig1.2 = (n_eq.rec_on sig.2) := begin
              simp [seq],
              cc
            end,
            contradiction
          end,
          exact decidable.is_false sneq
      end
  else 
    begin -- n ≠ n1
          let sneq : ¬sig=sig1 := begin
            assume seq:sig=sig1,
            induction sig, induction sig1,
            let : ¬sig_fst = sig1_fst := by cc,
            cc,
          end,
          exact decidable.is_false sneq
    end

    
def assignGeometryFrame  (sig : Σn:ℕ, euclideanGeometry n)
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
/-
inductive euclideanGeometryFrame
    {n : ℕ }  
    (sp : euclideanGeometry n) : Type
| std 
    : euclideanGeometryFrame
| derived 
    (fr : euclideanGeometryFrame)
    (origin : euclideanGeometryPoint sp)
    (basis : euclideanGeometryBasis sp)
    (m : MeasurementSystem)
    (or : AxisOrientation n)
    : euclideanGeometryFrame
| interpret
    (fr : euclideanGeometryFrame)
    (m : MeasurementSystem)
    (or : AxisOrientation n)
    : euclideanGeometryFrame
-/
instance fr_eq 
  {n}
  --{n1}
  {sp : euclideanGeometry n}
  --{sp1 : euclideanGeometry n}
  --{sig : Σn:ℕ, euclideanGeometry n}
  --{sig1 : Σn1:ℕ, euclideanGeometry n1}
  {fr : euclideanGeometryFrame sp}
  {fr1 : euclideanGeometryFrame sp}
  : decidable (fr=fr1)
  :=
  --let spl : euclideanGeometryFrame sp → euclideanGeometryFrame sp → decidable (fr=fr1) := sorry in
  --spl fr fr1
  begin
    cases fr,
    {
      cases fr1,
      { exact decidable.is_true rfl },
      { exact decidable.is_false (by contradiction) },
      { exact decidable.is_false (by contradiction) }
    },
    {
      cases fr1,
      
      { exact decidable.is_false (by contradiction) },
      { 
        let eqm := fr_m=fr1_m,
        cases (eqm:bool),

        exact decidable.is_true 
          begin
            --cases 
          end
      },
      { exact decidable.is_false (by contradiction) }
    },
    {
      cases fr1,
      { exact decidable.is_false (by contradiction) },
      { exact decidable.is_true rfl },
      { exact decidable.is_false (by contradiction) }
    }
  end
  --if n_eq : n=n1 then
  --  if fr
  --else 

/-
  if n_eq : sp=sp1 then 
    begin
      let t : sp = sp1 := begin
        induction sp,
        induction sp1,
        let : sp=sp1 := by cc,
        cc
      end,
      exact decidable.is_true t
    end  
  else
    begin
      let f : ¬(sp=sp1) := begin
        
        induction sp,
        induction sp1,
        let nsp : ¬(sp=sp1) := by cc,
        --by cc,
        simp *,
      end,
      exact decidable.is_false f
    end  
    -/

instance  tr_eq
  {sig : Σn,
        (Σs:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s,
                euclideanGeometryFrame s}
  {sig1 : Σn,
        (Σs1:euclideanGeometry n,
            Σfrom_:euclideanGeometryFrame s1,
                euclideanGeometryFrame s1}
  : decidable (sig=sig1)  := 
  begin
    exact (decidable.is_true sorry)
  end


noncomputable def assignGeometryTransform 
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

noncomputable def assignGeometryVector
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

noncomputable def assignGeometryPoint 
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

noncomputable def assignGeometryQuantity 
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
                

noncomputable def assignGeometryAngle 
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
                

noncomputable def assignGeometryOrientation
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
                

noncomputable def assignGeometryRotation
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
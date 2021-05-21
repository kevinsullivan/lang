import ..imperative_DSL.environment
import ..eval.timeEval

open lang.classicalTime

open measurementSystem
/-{
    t:={sp := (λ r,     
                if (spaceVarEq v r) 
                then (classicalTimeEval e i) 
                else (i.t.sp r)), ..i.t},
    ..i
  }-/
--open classical
--local attribute [instance] prop_decidable --makes everything noncomputable which is problematic



noncomputable def assignTimeSpace
  : environment.env → spaceVar → spaceExpr → environment.env
| i v e :=
  {
    t:={sp :=
                λ r,
                let d := (i.t.sp r) in
                if r.num = v.num then 
                    (classicalTimeEval e i)
                else d
                ..i.t},
    ..i
  }


noncomputable def assignTimeFrame (sp : classicalTime)
  : environment.env → lang.classicalTime.frameVar sp → lang.classicalTime.frameExpr sp → environment.env
| i v e := 
  {
    t:={fr := 
          λ sp1,
          λ v1,
            let d : classicalTimeFrame sp1 := (i.t.fr sp1 v1) in
            if v1.num = v.num then 
              if eqn:sp=sp1 then 
                let e1 : frameExpr sp1 := eq.rec e eqn in
                (classicalTimeFrameEval sp1 e1 i)
              else d
            else d,
            ..i.t},
    ..i
  }

noncomputable def assignTimeTransform
    (sig: Σs : classicalTime, Σ from_ : classicalTimeFrame s, classicalTimeFrame s)
     : environment.env → lang.classicalTime.TransformVar sig → 
          lang.classicalTime.TransformExpr sig → environment.env
| i v e := 
  {
    t:={tr := 
          λ sig1,
          λ v1,
            let d : classicalTimeTransform sig1.2.1 sig1.2.2 := (i.t.tr sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : TransformExpr sig1 := eq.rec e eqn in
                (classicalTimeFrameEval sig1 e1 i)
              else d
            else d,
            ..i.t},
    ..i
  }

noncomputable def assignTimeVector
    (sig: Σs : classicalTime, classicalTimeFrame s)
    : environment.env → lang.classicalTime.CoordinateVectorVar sig → 
          lang.classicalTime.CoordinateVectorExpr sig → environment.env 
| i v e := 
  {
    t:={vec := 
          λ sig1,
          λ v1,
            let d : classicalTimeCoordinateVector sig1.2 := (i.t.vec sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : CoordinateVectorExpr sig1 := eq.rec e eqn in
                (classicalTimeCoordinateVectorEval sig1 e1 i)
              else d
            else d,
            ..i.t},
    ..i
  }


noncomputable def assignTimePoint
    (sig: Σs : classicalTime, classicalTimeFrame s)
     : environment.env → lang.classicalTime.CoordinatePointVar sig → 
        lang.classicalTime.CoordinatePointExpr sig → environment.env 
| i v e := 
  {
    t:={pt := 
          λ sig1,
          λ v1,
            let d : classicalTimeCoordinatePoint sig1.2 := (i.t.pt sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : CoordinatePointExpr sig1 := eq.rec e eqn in
                (classicalTimeCoordinatePointEval sig1 e1 i)
              else d
            else d,
            ..i.t},
    ..i
  }

instance  sig_q_eq
  {sig: Σs : classicalTime, MeasurementSystem}
  {sig1: Σs : classicalTime, MeasurementSystem}
  : decidable (sig=sig1)  := 
  /-begin 
    let sp_eq := sig.1=sig1.1,
    let m_eq := sig.2 = sig1.2,
    cases (sp_eq:bool),
    {
      cases (m_eq:bool),
      {
        let seq : sig=sig1 := begin
          induction sig, induction sig1,
          simp *,
          exact and.intro sp_eq m_eq
        end
        
      },
      {

      }
    },
    {sorry}
  end-/
  if sp_eq : sig.1=sig1.1 then
    if m_eq : sig.2 = sig1.2 then
      begin
        let seq : sig = sig1 := begin
          induction sig, induction sig1,
          simp *,
          cc

        end,
        
      end
    else begin

    end
  else begin

  end

noncomputable def assignTimeQuantity
    (sig: Σs : classicalTime, MeasurementSystem)
     : environment.env → lang.classicalTime.QuantityVar sig → 
        lang.classicalTime.QuantityExpr sig → environment.env 
| i v e := 
  {
    t:={q := 
          λ sig1,
          λ v1,
            let d : classicalTimeQuantity sig1.1 sig1.2 := (i.t.q sig1 v1) in
            if v1.num = v.num then 
              if eqn:sig=sig1 then 
                let e1 : QuantityExpr sig1 := eq.rec e eqn in
                (classicalTimeQuantityEval sig1 e1 i)
              else d
            else d,
            ..i.t},
    ..i
  }
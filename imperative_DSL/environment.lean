--import ..expressions.classical_geometry
import ..expressions.classical_time
--import ..expressions.classical_velocity
import ..expressions.boolean
import ..expressions.measurementSystem
--import ..expressions.classical_acceleration

noncomputable theory

namespace environment
structure env : Type :=
mk ::   --(g: lang.classicalGeometry.spaceEnv)
        (t: lang.classicalTime.env)
        (ms: lang.measurementSystem.env)
        --(v: lang.classicalVelocity.env)
        --(a: lang.classicalAcceleration.env)

def init_env :env := --env.mk 
--                    lang.classicalGeometry.init
                   ⟨lang.classicalTime.initEnv, ⟨lang.measurementSystem.init⟩⟩
--                    lang.classicalVelocity.init
--                    lang.classicalAcceleration.init
end environment
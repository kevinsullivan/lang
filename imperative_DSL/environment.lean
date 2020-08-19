import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean

namespace environment
structure env : Type :=
mk ::   (g: lang.classicalGeometry.env)
        (t: lang.classicalTime.env)
        (v: lang.classicalVelocity.env)

def init_env := env.mk 
                    lang.classicalGeometry.init
                    lang.classicalTime.init 
                    lang.classicalVelocity.init
end environment
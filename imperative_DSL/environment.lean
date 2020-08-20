import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean
import ..expressions.classical_acceleration

namespace environment
structure env : Type :=
mk ::   (g: lang.classicalGeometry.env)
        (t: lang.classicalTime.env)
        (v: lang.classicalVelocity.env)
        (a: lang.classicalAcceleration.env)

def init_env := env.mk 
                    lang.classicalGeometry.init
                    lang.classicalTime.init 
                    lang.classicalVelocity.init
                    lang.classicalAcceleration.init

def classicalGeometryGet : env → lang.classicalGeometry.env
| (env.mk g t v a) := g
def classicalTimeGet : env → lang.classicalTime.env
| (env.mk g t v a) := t
def classicalVelocityGet : env → lang.classicalVelocity.env
| (env.mk g t v a) := v
def classicalAccelerationGet : env → lang.classicalAcceleration.env
| (env.mk g t v a) := a

end environment
import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean

structure env : Type :=
mk ::   (g: lang.classicalGeometry.env)
        (t: lang.classicalTime.env)
        (v: lang.classicalVelocity.env)

def init_env := env.mk 
                    lang.classicalGeometry.init
                    lang.classicalTime.init 
                    lang.classicalVelocity.init

def assignClassicalGeometry : env → lang.classicalGeometry.var → lang.classicalGeometry.expr → env
| (env.mk g t v) var expr := let r := (lang.classicalGeometry.override g var expr) 
                             in (env.mk r t v)


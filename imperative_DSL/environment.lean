import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_velocity
import ..expressions.boolean

structure env : Type :=
mk ::   (g: lang.classicalGeometry.env)
        (t: lang.classicalTime.env)
        (v: lang.classicalVelocity.env)

def classicalGeometryGet : env → lang.classicalGeometry.env
| (env.mk g t v ) := g
def classicalTimeGet : env → lang.classicalTime.env
| (env.mk g t v ) := t
def classicalVelocityGet : env → lang.classicalVelocity.env
| (env.mk g t v ) := v

def init_env := env.mk 
                    lang.classicalGeometry.init
                    lang.classicalTime.init 
                    lang.classicalVelocity.init

def assignClassicalGeometry : env → lang.classicalGeometry.var → lang.classicalGeometry.expr → env
| (env.mk g t v) var expr := let r := (lang.classicalGeometry.override g var expr) 
                             in (env.mk r t v)

def assignClassicalTime : env → lang.classicalTime.var → lang.classicalTime.expr → env
| (env.mk g t v) var expr := let r := (lang.classicalTime.override t var expr) in (env.mk g r v)

def assignClassicalVelocity : env → lang.classicalVelocity.var → lang.classicalVelocity.expr → env 
| (env.mk g t v) var expr := let r := (lang.classicalVelocity.override v var expr) in (env.mk g t r)

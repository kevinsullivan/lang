import .expr_base
import ...phys.geom.geom3d
import .scalar_expr


namespace lang.geom3d

universes u

structure geom3d_frame_var extends var 


inductive geom3d_frame_expr : Type 1 --{f : fm scalar T}
| lit (f : geom3d_frame) : geom3d_frame_expr
| var (v : geom3d_frame_var) : geom3d_frame_expr


abbreviation geom3d_frame_env :=
  geom3d_frame_var → geom3d_frame
abbreviation geom3d_frame_eval :=
  geom3d_frame_env → geom3d_frame_expr → geom3d_frame

def default_frame_env : geom3d_frame_env := 
  λv, geom3d_std_frame
def default_frame_eval : geom3d_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_frame_env expr_)
  end

def static_frame_eval : geom3d_frame_eval 
| env_ (geom3d_frame_expr.lit f) := f
| env_ (geom3d_frame_expr.var v) := env_ v

def geom3d_frame_expr.value (expr_ : geom3d_frame_expr) : geom3d_frame :=
  (static_frame_eval) (default_frame_env) expr_

structure geom3d_space_var (f : geom3d_frame_expr) extends var

inductive geom3d_space_expr (f : geom3d_frame_expr) : Type 1
| lit (sp : geom3d_space f.value) : geom3d_space_expr
| var (v : geom3d_space_var f) : geom3d_space_expr
| mk : geom3d_space_expr

abbreviation geom3d_space_env := Π(f : geom3d_frame_expr),
  geom3d_space_var f → geom3d_space f.value
abbreviation geom3d_space_eval := Π(f : geom3d_frame_expr),
  geom3d_space_env → geom3d_space_expr f → geom3d_space f.value


def default_space_env : geom3d_space_env := 
  λf, λv, mk_space f.value
def default_space_eval : geom3d_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_space_env f expr_),
    exact mk_space f.value
  end

def static_space_eval : geom3d_space_eval 
| f env_ (geom3d_space_expr.lit sp) := sp
| f env_ (geom3d_space_expr.var v) := env_ f v
| f env_ (geom3d_space_expr.mk) := mk_space f.value

def geom3d_space_expr.value {f : geom3d_frame_expr} (expr_ : geom3d_space_expr f)  : geom3d_space f.value :=
  (static_space_eval f) (default_space_env) expr_

/-
Transform
-/
structure transform_var  
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) extends var

inductive geom3d_transform_expr
  --{f1 : geom3d_frame} {f2 : geom3d_frame} (sp1 : geom3d_space f1) (sp2:=sp1 : geom3d_space f2) 
 -- (sp1 : Σf1 : geom3d_frame, geom3d_space f1)  (sp2 : Σf2 : geom3d_frame, geom3d_space f2 := sp1)
  : Π {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1), Π {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2), Type 1
| lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (p : geom3d_transform sp1.value sp2.value) : geom3d_transform_expr sp1 sp2
| var {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : transform_var sp1 sp2) : geom3d_transform_expr sp1 sp2
| compose_lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame} {sp2 : geom3d_space f2} (t1 : geom3d_transform sp1.value sp2) 
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3}  (t2 : geom3d_transform sp2 sp3.value) : geom3d_transform_expr sp1 sp3
| inv_lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (t : geom3d_transform sp2.value sp1.value) : geom3d_transform_expr sp1 sp2
| compose 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1}
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3}
  (t1 : geom3d_transform_expr sp1 sp3) (t2 : geom3d_transform_expr sp3 sp2) : geom3d_transform_expr sp1 sp2
| inv
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1}
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (tr : geom3d_transform_expr sp2 sp1) : geom3d_transform_expr sp1 sp2

class geom3d_transform_has_lit 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (cast : geom3d_transform sp1.value sp2.value → geom3d_transform_expr sp1 sp2)
notation `|`tlit`|` := geom3d_transform_has_lit.cast tlit

instance geom3d_transform_lit 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} : geom3d_transform_has_lit sp1 sp2 := 
  ⟨λt, geom3d_transform_expr.lit t⟩

abbreviation transform_env 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)  := 
  transform_var sp1 sp2 → geom3d_transform sp1.value sp2.value

abbreviation transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  transform_env sp1 sp2 → geom3d_transform_expr sp1 sp2 → geom3d_transform sp1.value sp2.value


def default_transform_env 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) 
    : transform_env sp1 sp2:=
    λv, (sp1.value).mk_geom3d_transform_to sp2.value

def default_transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.mk_geom3d_transform_to sp2.value

def static_transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) : transform_eval sp1 sp2 
| env_ (geom3d_transform_expr.lit tr) := tr
| env_ (geom3d_transform_expr.var v) := env_ v
| env_ (geom3d_transform_expr.compose_lit t1 t2) := ⟨⟨t1.1.1.trans t2.1.1⟩⟩
| env_ (geom3d_transform_expr.inv_lit t) := ⟨⟨(t.1.1).symm⟩⟩
| env_ expr_ := default_transform_eval sp1 sp2 (default_transform_env sp1 sp2) expr_

def geom3d_transform_expr.value {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (expr_ : geom3d_transform_expr sp1 sp2) : geom3d_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (default_transform_env sp1 sp2) expr_)

variables {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
          (expr_ : geom3d_transform_expr sp1 sp2)

#check expr_.value

--INVERSE CANNOT BE DEEPLY EMBEDDED - IT HAS A DIFFERENT TYPE

/-
class transform_has_inv 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (inv : geom3d_transform_expr sp1 sp2 → geom3d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

instance transform_inv {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
      let ftr := lit.1,
      let mtr := ftr.1.symm,
      let invlit : geom3d_transform sp2.value sp1.value := ⟨⟨mtr⟩⟩,
      exact [invlit]
    end
-/
class transform_has_inv 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (inv : geom3d_transform_expr sp1 sp2 → geom3d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

instance transform_inv {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
     -- let ftr := lit.1,
     -- let mtr := ftr.1.symm,
     -- let invlit : geom3d_transform sp2.value sp1.value := ⟨⟨mtr⟩⟩,
     exact (geom3d_transform_expr.inv_lit lit),
    end⟩


def geom3d_transform_expr.trans 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
 {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3} (expr_ : geom3d_transform_expr sp1 sp2) : geom3d_transform_expr sp2 sp3 → geom3d_transform_expr sp1 sp3 
 := λt2,
 geom3d_transform_expr.compose_lit expr_.value t2.value

--instance scalar_lit (sp : scalar_expr) : scalar_has_lit  sp := 
--  ⟨λt : scalar, scalar_expr.lit t⟩
/-
Duration
-/
structure displacement3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var 

/-
Time
-/
structure position3d_var  {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var
set_option trace.app_builder true --need to fix scalar for this to work

mutual inductive displacement3d_expr, position3d_expr {f : geom3d_frame_expr} (sp : geom3d_space_expr f)
with displacement3d_expr : Type 1
| zero : displacement3d_expr
| one : displacement3d_expr 
| lit (v : displacement3d sp.value) : displacement3d_expr
| var (v : displacement3d_var sp) : displacement3d_expr
| add_dur_dur (d1 : displacement3d_expr) (d2 : displacement3d_expr) : displacement3d_expr
| neg_dur (d : displacement3d_expr) : displacement3d_expr
| sub_dur_dur (d1 : displacement3d_expr) (d2 : displacement3d_expr) : displacement3d_expr
| sub_position3d_position3d (t1 : position3d_expr) (t2 : position3d_expr) : displacement3d_expr
| smul_dur (k : scalar_expr) (d : displacement3d_expr) : displacement3d_expr
| apply_displacement3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (d : displacement3d sp2.value) : displacement3d_expr
with position3d_expr : Type 1
| lit (p : position3d sp.value) : position3d_expr
| var (v : position3d_var sp) : position3d_expr
| add_dur_position3d (d : displacement3d_expr) (t : position3d_expr) : position3d_expr
| apply_position3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (t : position3d sp2.value) : position3d_expr


abbreviation displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  displacement3d_var sp → displacement3d sp.value

attribute [elab_as_eliminator] 
abbreviation position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  position3d_var sp → position3d sp.value

abbreviation displacement3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  position3d_env sp → displacement3d_env sp → displacement3d_expr sp → displacement3d sp.value

abbreviation position3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f), 
  position3d_env sp → displacement3d_env sp → position3d_expr sp → position3d sp.value

def default_displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_env sp := λv, (mk_displacement3d sp.value 1 1 1)
def default_displacement3d_eval : displacement3d_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    --cases expr_,
    --exact expr_,
    --exact default_displacement3d_env sp expr_,
    repeat {exact (mk_displacement3d sp.value 1 1 1)}
  end

--this needs to get fixed, perhaps eval should not depend on env but use a global one *shrug*
--OR, a point evaluator needs to depend on a vector environment, and vice versa? may be acceptable
def default_position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_env sp 
  := (λv, (mk_position3d sp.value  1 1 1))


set_option eqn_compiler.max_steps 8192
mutual def static_displacement3d_eval, static_position3d_eval 
with static_displacement3d_eval : displacement3d_eval 
| f sp tenv_ denv_ (displacement3d_expr.zero) := 0
| f sp tenv_ denv_ (displacement3d_expr.one) := mk_displacement3d sp.value 1 1 1
| f sp tenv_ denv_ (displacement3d_expr.lit d) := d
| f sp tenv_ denv_ (displacement3d_expr.var v) := denv_ v
| f sp tenv_ denv_ (displacement3d_expr.add_dur_dur d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) +ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_expr.neg_dur d) := -(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_expr.sub_dur_dur d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) -ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_expr.sub_position3d_position3d t1 t2) := (static_position3d_eval sp tenv_ denv_ t1) -ᵥ (static_position3d_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (displacement3d_expr.smul_dur s d) := (static_scalar_eval default_scalar_env s)•(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_expr.apply_displacement3d_lit t d) := t.value.transform_displacement3d d
with static_position3d_eval : position3d_eval
| f sp tenv_ denv_ (position3d_expr.lit p) := p
| f sp tenv_ denv_ (position3d_expr.var v) := tenv_ v
| f sp tenv_ denv_ (position3d_expr.add_dur_position3d d t) := (static_displacement3d_eval sp tenv_ denv_ d) +ᵥ (static_position3d_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (position3d_expr.apply_position3d_lit tr t) := tr.value.transform_position3d t


def default_position3d_eval : position3d_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_position3d_env sp expr_,
    repeat {exact (mk_position3d sp.value 1 1 1)}
  end

#check position3d_env
#check default_position3d_env

def position3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : position3d_expr sp) : position3d sp.value :=
  (static_position3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_

def displacement3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : displacement3d_expr sp) : displacement3d sp.value :=
  (static_displacement3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_


--not working -- lean doesn't play nice with notation and dependent types
--notation `|`flit`|` := geom3d_frame_expr.lit flit
--notation `|`slit`|` := geom3d_space_expr.lit slit
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : geom3d_frame} {sp : geom3d_space f} : has_coe (position3d sp) (position3d_expr sp) := ⟨λt, position3d_expr.lit t⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : geom3d_frame} {sp : geom3d_space f} : has_coe (displacement3d sp) (displacement3d_expr sp) := ⟨λt, displacement3d_expr.lit t⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] : has_coe (geom3d_frame) (geom3d_frame_expr scalar) := ⟨λf, geom3d_frame_expr.lit f⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : geom3d_frame} : has_coe (geom3d_space f) (geom3d_space_expr scalar) := ⟨λs, geom3d_space_expr.lit s⟩

/-
class has_lit (t1 : Type 0) (t2 : Type 1) :=
  (cast : t1 → t2)
notation `|`lit`|` := has_lit.cast lit
instance position3d_lit {f : geom3d_frame_expr} {sp : geom3d_space_expr f } : has_lit (position3d sp.value) (position3d_expr sp) :=
  ⟨λt, position3d_expr.lit t⟩
instance displacement3d_lit {f : geom3d_frame_expr} {sp : geom3d_space_expr f } : has_lit (displacement3d sp.value) (displacement3d_expr sp) :=
  ⟨λd, displacement3d_expr.lit d⟩
instance position3d_space_lit {f : geom3d_frame_expr} : has_lit (geom3d_space f.value) (geom3d_space_expr f) :=
  ⟨λs, geom3d_space_expr.lit s⟩
instance position3d_frame_lit : has_lit (geom3d_frame) (geom3d_frame_expr) :=
  ⟨λf, geom3d_frame_expr.lit f⟩
-/

class position3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : position3d sp.value → position3d_expr sp)
notation `|`tlit`|` := position3d_has_lit.cast tlit

instance position3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_has_lit  sp := 
  ⟨λt : position3d sp.value, position3d_expr.lit t⟩

class displacement3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : displacement3d sp.value → displacement3d_expr sp)
notation `|`tlit`|` := displacement3d_has_lit.cast tlit

instance displacement3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_has_lit  sp := 
  ⟨λt : displacement3d sp.value, displacement3d_expr.lit t⟩

class position3d_frame_has_lit := 
  (cast : geom3d_frame → geom3d_frame_expr)
notation `|`flit`|` := position3d_frame_has_lit.cast flit

instance position3d_frame_lit : position3d_frame_has_lit := 
  ⟨λf, geom3d_frame_expr.lit f⟩

class position3d_space_has_lit (f : geom3d_frame_expr ) := 
  (cast : geom3d_space f.value  → geom3d_space_expr f)
notation `|`slit`|` := position3d_space_has_lit.cast slit

instance position3d_space_lit {f : geom3d_frame_expr} : position3d_space_has_lit f := 
  ⟨λs, geom3d_space_expr.lit s⟩


variables  {f : geom3d_frame_expr} {sp : geom3d_space_expr f} 


/-
Analogous methods provided at math layer
-/
#check mk_frame

#check mk_frame
def mk_geom3d_frame_expr {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (o : position3d_expr sp) (b : displacement3d_expr sp) : geom3d_frame_expr :=
  |(mk_geom3d_frame o.value b.value)|
/-
4/7
WRITE THIS FUNCTION LATER. 
YOU NEED TO GET THE VALUE OUT OF THE f PARAMETER TO INCLUDE IT IN THE TYPE
AND THEN USE IT IN THE CONSTRUCTOR
-/
#check mk_space 
def mk_geom3d_space_expr (f : geom3d_frame_expr) : geom3d_space_expr f :=
  geom3d_space_expr.mk



def add_dur_expr_dur_expr (v1 v2 : displacement3d_expr sp) : displacement3d_expr sp := 
  displacement3d_expr.add_dur_dur v1 v2

def smul_dur_expr (k : scalar_expr) (v : displacement3d_expr sp) : displacement3d_expr sp := 
    displacement3d_expr.smul_dur k v

def neg_dur_expr (v : displacement3d_expr sp) : displacement3d_expr sp := 
    displacement3d_expr.neg_dur v

def sub_dur_expr_dur_expr (v1 v2 : displacement3d_expr sp) : displacement3d_expr sp :=    -- v1-v2
    displacement3d_expr.sub_dur_dur v1 v2

-- See unframed file for template for proving vector_space
instance has_one_dur_expr : has_one (displacement3d_expr sp) := ⟨displacement3d_expr.one⟩

instance has_add_dur_expr : has_add (displacement3d_expr sp) := ⟨ add_dur_expr_dur_expr ⟩

/-
THIS IS UNPROVABLE
-/
lemma add_assoc_dur_expr : ∀ a b c : displacement3d_expr sp, a + b + c = a + (b + c) :=
begin
    intros,
    cases a,
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 
      
    }
end

instance add_semigroup_dur_expr : add_semigroup (displacement3d_expr sp) := ⟨ add_dur_expr_dur_expr, add_assoc_dur_expr⟩ 

def dur_expr_zero : displacement3d_expr sp := displacement3d_expr.zero--displacement3d_expr.lit (mk_displacement3d sp.value 0)
instance has_zero_dur_expr : has_zero (displacement3d_expr sp) := ⟨dur_expr_zero⟩

lemma zero_add_dur_expr : ∀ a : displacement3d_expr sp, 0 + a = a := sorry
lemma add_zero_dur_expr : ∀ a : displacement3d_expr sp, a + 0 = a := sorry
instance add_monoid_dur_expr : add_monoid (displacement3d_expr sp) := ⟨ 
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    sorry,--@zero_add_dur_expr _ _ f sp, 
    add_zero_dur_expr
⟩

instance has_neg_dur_expr : has_neg (displacement3d_expr sp) := ⟨neg_dur_expr⟩
instance has_sub_dur_expr : has_sub (displacement3d_expr sp) := ⟨ sub_dur_expr_dur_expr⟩ 
lemma sub_eq_add_neg_dur_expr : ∀ a b : displacement3d_expr sp, a - b = a + -b := sorry
instance sub_neg_monoid_dur_expr : sub_neg_monoid (displacement3d_expr sp) := ⟨ 
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, 
    zero_add_dur_expr, 
    add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr,                                                       -- new
⟩ 

lemma add_left_neg_dur_expr : ∀ a : displacement3d_expr sp, -a + a = 0 := sorry
instance : add_group (displacement3d_expr sp) := ⟨
    -- sub_neg_monoid
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    -- new
    add_left_neg_dur_expr,
⟩ 

lemma add_comm_dur_expr : ∀ a b : displacement3d_expr sp, a + b = b + a := sorry
instance add_comm_semigroup_dur_expr : add_comm_semigroup (displacement3d_expr sp) := ⟨
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr,
    add_comm_dur_expr,
⟩

instance add_comm_monoid_dur_expr : add_comm_monoid (displacement3d_expr sp) := ⟨
-- add_monoid
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    zero_add_dur_expr, 
    add_zero_dur_expr,
-- add_comm_semigroup (minus repeats)
    add_comm_dur_expr,
⟩

instance has_scalar_dur_expr : has_scalar scalar_expr (displacement3d_expr sp) := ⟨
smul_dur_expr,
⟩
instance : has_one scalar_expr := sorry
instance : monoid scalar_expr := sorry
instance : has_zero scalar_expr := sorry

lemma one_smul_dur_expr : ∀ b : displacement3d_expr sp, (1 : scalar_expr) • b = b := sorry
lemma mul_smul_dur_expr : ∀ (x y : scalar_expr) (b : displacement3d_expr sp), (x * y) • b = x • y • b := sorry
instance mul_action_dur_expr : mul_action scalar_expr (displacement3d_expr sp) := sorry /-⟨
one_smul_dur_expr,
mul_smul_dur_expr,
⟩ -/

lemma smul_add_dur_expr : ∀(r : scalar_expr) (x y : displacement3d_expr sp), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_dur_expr : ∀(r : scalar_expr), r • (0 : displacement3d_expr sp) = 0 := sorry
instance distrib_mul_action_K_dur_exprKx : distrib_mul_action scalar_expr (displacement3d_expr sp) := ⟨
smul_add_dur_expr,
smul_zero_dur_expr,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_dur_expr : ∀ (a b : scalar_expr) (x : displacement3d_expr sp), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_dur_expr : ∀ (x : displacement3d_expr sp), (0 : scalar_expr) • x = 0 := sorry
instance semimodule_K_displacement3dK : semimodule scalar_expr (displacement3d_expr sp) := ⟨ add_smul_dur_expr, zero_smul_dur_expr ⟩ 

instance add_comm_group_dur_expr : add_comm_group (displacement3d_expr sp) := ⟨
-- add_group
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    add_left_neg_dur_expr,
-- commutativity
    add_comm_dur_expr,
⟩


instance : vector_space scalar (displacement3d_expr sp) := sorry


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement3d_expr sp) := ⟨add_dur_expr_dur_expr⟩
instance : has_zero (displacement3d_expr sp) := ⟨dur_expr_zero⟩
instance : has_neg (displacement3d_expr sp) := ⟨neg_dur_expr⟩

/-
Lemmas needed to implement affine space API
-/

def sub_position3d_expr_position3d_expr {f : geom3d_frame_expr} {sp : geom3d_space_expr f}  (p1 p2 : position3d_expr sp) : displacement3d_expr sp := 
    displacement3d_expr.sub_position3d_position3d p1 p2
def add_position3d_expr_dur_expr {f : geom3d_frame_expr} {sp : geom3d_space_expr f}  (p : position3d_expr sp) (v : displacement3d_expr sp) : position3d_expr sp := 
    position3d_expr.add_dur_position3d v p
def add_dur_expr_position3d_expr {f : geom3d_frame_expr} {sp : geom3d_space_expr f}  (v : displacement3d_expr sp) (p : position3d_expr sp) : position3d_expr sp := 
    position3d_expr.add_dur_position3d v p

def aff_dur_expr_group_action {f : geom3d_frame_expr} {sp : geom3d_space_expr f} : displacement3d_expr sp → position3d_expr sp → position3d_expr sp := add_dur_expr_position3d_expr
instance {f : geom3d_frame_expr} {sp : geom3d_space_expr f} : has_vadd (displacement3d_expr sp) (position3d_expr sp) := ⟨λd, λt, position3d_expr.add_dur_position3d d t⟩

def spf : geom3d_space_expr [geom3d_std_frame] := [(geom3d_std_space)]

variables (d d2 : displacement3d_expr spf) (t : position3d_expr spf) (df : displacement3d_expr spf)

#check position3d_expr.add_dur_position3d d t

lemma zero_dur_expr_vadd'_a1 {f : geom3d_frame_expr} {sp : geom3d_space_expr f} : ∀ p : position3d_expr sp, (0 : displacement3d_expr sp) +ᵥ p = p := sorry
lemma dur_expr_add_assoc'_a1 : ∀ (g1 g2 : displacement3d_expr sp) (p : position3d_expr sp), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance dur_expr_add_action: add_action (displacement3d_expr sp) (position3d_expr sp) := 
⟨ aff_dur_expr_group_action, zero_dur_expr_vadd'_a1, dur_expr_add_assoc'_a1 ⟩ 

def aff_position3d_expr_group_sub : position3d_expr sp → position3d_expr sp → displacement3d_expr sp := sub_position3d_expr_position3d_expr
instance position3d_expr_has_vsub : has_vsub (displacement3d_expr sp) (position3d_expr sp) := ⟨ aff_position3d_expr_group_sub ⟩ 


instance : nonempty (position3d_expr sp) := ⟨position3d_expr.lit (mk_position3d sp.value  0)⟩

lemma position3d_expr_vsub_vadd_a1 : ∀ (p1 p2 : (position3d_expr sp)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma position3d_expr_vadd_vsub_a1 : ∀ (g : displacement3d_expr sp) (p : position3d_expr sp), g +ᵥ p -ᵥ p = g := sorry
instance aff_position3d_expr_torsor : add_torsor (displacement3d_expr sp) (position3d_expr sp) := --affine space! 
⟨ 
    aff_dur_expr_group_action,
    zero_dur_expr_vadd'_a1,    -- add_action
    dur_expr_add_assoc'_a1,   -- add_action
    aff_position3d_expr_group_sub,    -- has_vsub
    position3d_expr_vsub_vadd_a1,     -- add_torsor
    position3d_expr_vadd_vsub_a1,     -- add_torsor
⟩

notation t+ᵥv := add_dur_expr_position3d_expr v t
notation d•k :=  smul_dur_expr k d
notation tr⬝d := displacement3d_expr.apply_displacement3d_lit tr d
notation tr⬝t := position3d_expr.apply_position3d_lit tr t

end lang.geom3d

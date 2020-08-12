import ...phys.src.geometry

structure classicalGeometryVar : Type := 
mk :: (num : ℕ) 

def classicalGeometryVarEq : classicalGeometryVar → classicalGeometryVar → bool
| v1 v2 := v1.num=v2.num

inductive classicalGeometryExpression
| GeometricSpaceLiteral (s : classicalGeometry) : classicalGeometryExpression
| GeometricSpaceVariable (v : classicalGeometryVar) : classicalGeometryExpression
--| GeometricProduct (e1 e2 : classicalGeometryExpression) : classicalGeometryExpression

def classicalGeometryEnvironment := (classicalGeometryVar → classicalGeometry)

def classicalGeometryEval : classicalGeometryExpression → classicalGeometryEnvironment → Space.classicalGeometry 
| (classicalGeometryExpression.GeometricSpaceLiteral s) e := s
| (classicalGeometryExpression.GeometricSpaceVariable v) e := e v
--| (classicalGeometryExpression.GeometricProduct V1 V2) E := V1 --not sure how to combine spaces yet




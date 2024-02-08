import Mathlib.Data.Real.Basic

import Mathlib.Data.Matrix.Notation

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup


abbrev r_3 := Fin 3 -> ℝ
def zero_one_zero : r_3 := ![0,1,0]

def rotate (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  (p : Matrix (Fin 3) (Fin 3) Real).vecMul vec

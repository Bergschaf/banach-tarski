import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

set_option maxHeartbeats 200000
inductive Generators where
  | a : Generators
  | b : Generators
  deriving DecidableEq
open Generators

--noncomputable def matrix_a := Matrix.smul_of (1/3) !![3, 0, 0; 0, 1,-2*Real.sqrt 2; 0, 2*Real.sqrt 2, 1]
--noncomputable def matrix_a' := Matrix.smul_of (1/3) !![1, -2*Real.sqrt 2, 0;( 2*Real.sqrt 2),1, 0; 0, 0, 3]
--noncomputable def matrix_b := Matrix.smul_of (1/3) !![3, 0, 0; 0, 1,-2*Real.sqrt 2; 0, 2*Real.sqrt 2, 1]
--noncomputable def matrix_b' := Matrix.smul_of (1/3) !![1, -2*Real.sqrt 2, 0;( -2*Real.sqrt 2),1, 0; 0, 0, 3]
--noncomputable def generator_value (g : (Generators ×  Bool)) :=
--  match g with
--   | (Generators.a, true) => matrix_a
--   | (Generators.b, true) => matrix_a'
--   | (Generators.a, false) => matrix_b
--   | (Generators.b, false) => matrix_b'


--theorem: FreeGroup.toWord_one{α : Type u} [DecidableEq α] :
--  FreeGroup.toWord 1 = []
def f2 := {w: FreeGroup Generators | true}
def e := {w: FreeGroup Generators | (FreeGroup.toWord w) = []}
def s_a := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.a, true)}
def s_b := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.b, true)}
def s_a' := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.a, false)}
def s_b' := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.b, false)}


theorem about_s_a (z : FreeGroup Generators) : z ∈ s_a -> ((FreeGroup.toWord z).head? = .some (Generators.a, true)) := by
  intro x
  use x
#check f2

theorem s_a_in_f2 : x ∈ s_a -> x ∈ f2 := by
  intro h
  sorry


theorem union_f2 : s_a ∪ s_b ∪ s_a' ∪ s_b' ∪ e = f2 := by
  apply subset_antisymm
  intro x h
  sorry
  sorry



---theorem s_a_in_FreeGroup (s := s_a) (w : FreeGroup Generators) : (FreeGroup.toWord w).head? = (Generators.a, true) -> w ∈ s_a :=

---  sorry

--------------------

--def r_3_set := Set r_3
theorem sq_2_mul_sq_2_eq_2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  norm_num

set_option maxHeartbeats 200000

noncomputable section
def matrix_a : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,-2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a' : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0;( 2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
def matrix_b' :Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0;( -2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1, 0; 0, 0, 1]
---def matritzen : Set (Matrix (Fin 3) (Fin 3) Real) := {matrix_a, matrix_b, matrix_a', matrix_b', matrix_one}


theorem matrix_inverse :  matrix_a * matrix_a' = matrix_one := by
  sorry



theorem matrix_a_det_neq_zero : Matrix.det matrix_a ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry

theorem matrix_b_det_neq_zero : Matrix.det matrix_b ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry


def gl_a : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a matrix_a_det_neq_zero
def gl_b : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b matrix_b_det_neq_zero

def G := Subgroup.closure {gl_a, gl_b}


abbrev r_3 := Fin 3 -> ℝ

def rotate (matrix : Matrix (Fin 3) (Fin 3) Real) (vec : r_3) : r_3 :=
  matrix.mulVec vec


def zero_one_zero : r_3 := ![0,1,0]
def a_b_c_vec (a b c : Real) (n : Nat) : r_3 :=
  1/3^n * ![a * Real.sqrt 2, b, c * Real.sqrt 2]

theorem lemma_3_1 (p: GL (Fin 3) Real) (h: p ∈ G) (a b c: Real) (n : Nat):
       ∃ a b c, ∃ n, rotate p zero_one_zero = a_b_c_vec a b c n:= by
  rw [rotate]
  induction n with
    | zero =>
    use 0
    use 1
    use 0
    use 0
    rw [a_b_c_vec]
    rw [zero_mul]
    simp
    have a : p = matrix_one := by

      sorry
    sorry
    | succ d hd => sorry


---def matrix_group := {w: GL (Fin 3) Real | true}

theorem matritzen_in_GL : ∀ x ∈ matritzen, x ∈ matrix_group :=
  sorry

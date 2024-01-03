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
import Mathlib.Data.Set.Card

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

set_option maxHeartbeats 0
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

set_option maxHeartbeats 0

noncomputable section
def matrix_a : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,-2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a' : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0;( 2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
def matrix_b' :Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0;( -2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
---def matritzen : Set (Matrix (Fin 3) (Fin 3) Real) := {matrix_a, matrix_b, matrix_a', matrix_b', matrix_one}


theorem matrix_inverse :  matrix_a * matrix_a' = matrix_one := by
  sorry



theorem matrix_a_det_neq_zero : Matrix.det matrix_a ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry

theorem matrix_a'_det_neq_zero : Matrix.det matrix_a' ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry


theorem matrix_b_det_neq_zero : Matrix.det matrix_b ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry

theorem matrix_b'_det_neq_zero : Matrix.det matrix_b' ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry

theorem matrix_one_det_neq_zero : Matrix.det matrix_one ≠ 0 := by
  norm_num
  refine Matrix.nondegenerate_iff_det_ne_zero.mp ?_
  sorry

def gl_a  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a matrix_a_det_neq_zero
def gl_b  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b matrix_b_det_neq_zero
def gl_a'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a' matrix_a'_det_neq_zero
def gl_b'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b' matrix_b'_det_neq_zero
def gl_one  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_one matrix_one_det_neq_zero




def a_inv_a' :=
  gl_a * gl_a' = matrix_one

def b_inv_b' :=
  gl_b * gl_b' = matrix_one

def gl_ab : Set (GL (Fin 3) Real) := {gl_a, gl_a', gl_b, gl_b', gl_one}
--abbrev gl_subtype :=  {w : GL (Fin 3) Real | w ∈ gl_ab}

def erzeuger : Set (GL (Fin 3) Real) := {gl_a, gl_b, gl_one}

def G := Subgroup.closure erzeuger

abbrev r_3 := Fin 3 -> ℝ
#check G
def zero_one_zero : r_3 := ![0,1,0]
def gl_to_m (matrix: GL (Fin 3) Real) : Matrix (Fin 3) (Fin 3) Real := matrix

def gl_to_m_one_eq_one : gl_to_m 1 = matrix_one := by
  rw [gl_to_m]
  rw [@Units.val_one]
  rw [matrix_one]


def gl_to_m_gl_one_eq_one : gl_to_m gl_one = matrix_one := by
  rfl
def gl_to_m_a_eq_a : gl_to_m gl_a = matrix_a := by
  rfl
def gl_to_m_b_eq_b : gl_to_m gl_b = matrix_b := by
  rfl


def rotate_g (word : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  (gl_to_m word).vecMul vec


def a_b_c_vec (a b c : Real) (n : Nat) : r_3 :=
   ![1/3^n * a * Real.sqrt 2,1/3^n * b,1/3^n * c * Real.sqrt 2]



theorem case_one : ∃ a b c n, rotate_g 1 zero_one_zero = a_b_c_vec a b c n := by
    rw [rotate_g]
    use 0
    use 1
    use 0
    use 0
    rw [a_b_c_vec]
    simp
    rw [zero_one_zero]
    rw [gl_to_m_one_eq_one]
    rw [matrix_one]
    simp

  theorem case_gl_one : ∃ a b c n, rotate_g gl_one zero_one_zero = a_b_c_vec a b c n := by
    rw [rotate_g]
    use 0
    use 1
    use 0
    use 0
    rw [a_b_c_vec]
    simp
    rw [zero_one_zero]
    rw [gl_to_m_gl_one_eq_one]
    rw [matrix_one]
    simp

theorem case_a (x) (h: x = gl_a): ∃ a b c n, rotate_g x zero_one_zero = a_b_c_vec a b c n := by
    rw [h]
    rw [rotate_g]
    rw [gl_to_m_a_eq_a]
    rw [zero_one_zero]
    rw [matrix_a]
    use 0
    use 1
    use -2
    use 1
    rw [a_b_c_vec]
    simp
    norm_num


theorem case_b (x) (h: x = gl_b): ∃ a b c n, rotate_g x zero_one_zero = a_b_c_vec a b c n := by
    rw [h]
    rw [rotate_g]
    rw [gl_to_m_b_eq_b]
    rw [zero_one_zero]
    rw [matrix_b]
    use 2
    use 1
    use 0
    use 1
    rw [a_b_c_vec]
    simp
    norm_num



def hk (x : GL (Fin 3) Real) (h: x ∈ erzeuger): ∃ a b c n, rotate_g x zero_one_zero = a_b_c_vec a b c n := by
 cases h with
 | inl ha =>
 apply case_a
 exact ha
 | inr hx =>
 cases hx with
 | inl hb =>
  apply case_b
  exact hb
 | _ hc =>
  rw [hc]
  apply case_gl_one


def G_one : G := 1
theorem h_one : ∃ a b c n, rotate_g G_one zero_one_zero = a_b_c_vec a b c n := by
  apply case_one

theorem h_mul (x y) (h1: ∃ a b c n, rotate_g x zero_one_zero = a_b_c_vec a b c n)
(h2 :∃ e f g m, rotate_g y zero_one_zero = a_b_c_vec e f g m) :
∃ j k i o, rotate_g (x*y) zero_one_zero = a_b_c_vec j k i o := by
  rw [rotate_g]
  rw [gl_to_m]
  rw [@Matrix.GeneralLinearGroup.coe_mul]
  rw [zero_one_zero]

  rw [rotate_g] at h1
  rw [gl_to_m] at h1
  rw [zero_one_zero] at h1

  rw [rotate_g] at h2
  rw [gl_to_m] at h2
  rw [zero_one_zero] at h2

  rcases h1 with ⟨a, b, c, n, h1'⟩
  rcases h2 with ⟨e, f, g, m, h2'⟩


  sorry



def h_inv (x) (h1:∃ a b c n, rotate_g x zero_one_zero = a_b_c_vec a b c n) :
  ∃ a b c n, rotate_g (x⁻¹) zero_one_zero = a_b_c_vec a b c n := by
  rw [rotate_g]
  rw [gl_to_m]
  rw [zero_one_zero]

  rw [rotate_g] at h1
  rw [gl_to_m] at h1
  rw [zero_one_zero] at h1

  rcases h1 with ⟨a, b, c, n, h1'⟩
  simp






theorem lemma_3_1 (p: GL (Fin 3) Real) (h: p ∈ G):
       ∃ a b c n, rotate_g p zero_one_zero = a_b_c_vec a b c n:=
  Subgroup.closure_induction h hk h_one h_mul h_inv

#check lemma_3_1








---def matrix_group := {w: GL (Fin 3) Real | true}

theorem matritzen_in_GL : ∀ x ∈ matritzen, x ∈ matrix_group :=
  sorry

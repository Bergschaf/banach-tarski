import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

import Mathlib.Data.Matrix.Reflection

set_option maxHeartbeats 0


noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a'  : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_b'  : Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0; (-2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
end noncomputable section

theorem matrix_a_inverse :  matrix_a * matrix_a' = matrix_one := by
  rw [matrix_a]
  rw [matrix_a']
  rw [matrix_one]
  norm_num
  ext h1 h2
  fin_cases h1
  simp
  rw [@Matrix.one_fin_three]
  simp

  simp
  norm_num
  rw [@mul_mul_mul_comm]
  norm_num
  simp
  rw [div_eq_mul_inv]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [@Mathlib.Tactic.RingNF.add_neg]
  rw [@mul_assoc]
  rw [mul_comm 3⁻¹]
  rw [mul_comm 3⁻¹]
  rw [← mul_assoc]
  rw [sub_self]
  rw [@Matrix.one_fin_three]
  simp

  simp
  ring
  simp
  rw [Real.sq_sqrt]
  ring
  rw [@Matrix.one_fin_three]
  exact rfl
  norm_num

theorem matrix_a_det_neq_zero : Matrix.det matrix_a ≠ 0 := by
  rw [matrix_a]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring
  simp
  rw [Real.sq_sqrt]
  norm_num
  norm_num

theorem matrix_a'_det_neq_zero : Matrix.det matrix_a' ≠ 0 := by
  rw [matrix_a']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring
  simp
  rw [Real.sq_sqrt]
  norm_num
  norm_num

theorem matrix_b_det_neq_zero : Matrix.det matrix_b ≠ 0 := by
  rw [matrix_b]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring
  simp
  rw [Real.sq_sqrt]
  norm_num
  norm_num

theorem matrix_b'_det_neq_zero : Matrix.det matrix_b' ≠ 0 := by
  rw [matrix_b']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring
  simp
  rw [Real.sq_sqrt]
  norm_num
  norm_num

theorem matrix_one_det_neq_zero : Matrix.det matrix_one ≠ 0 := by
  rw [matrix_one]
  rw [Matrix.det_fin_three]
  simp

noncomputable section
def gl_a   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a matrix_a_det_neq_zero
def gl_a'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a' matrix_a'_det_neq_zero
def gl_b   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b matrix_b_det_neq_zero
def gl_b'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b' matrix_b'_det_neq_zero
def gl_one : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_one matrix_one_det_neq_zero
end noncomputable section


def erzeuger : Set (GL (Fin 3) Real) := {gl_a, gl_b, gl_one}

def G := Subgroup.closure erzeuger

abbrev r_3 := Fin 3 -> ℝ
def zero_one_zero : r_3 := ![0,1,0]


def coe_gl_one_eq_one : ↑gl_one = 1 := by
  exact Units.val_eq_one.mp rfl

def coe_gl_a_eq_matrix_a : ↑gl_a = matrix_a := by
  rfl

def coe_gl_b_eq_matrix_b : ↑gl_b = matrix_b := by
  rfl


def rotate (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  (p : Matrix (Fin 3) (Fin 3) Real).vecMul vec


def a_b_c_vec (a b c : ℤ) (n : Nat) : r_3 :=
   ![1/3^n * a * Real.sqrt 2,1/3^n * b,1/3^n * c * Real.sqrt 2]

def general_word_form  (a b c d e f g h i : ℤ) : Matrix (Fin 3) (Fin 3) Real :=
  !![(a : Real),b * Real.sqrt 2, c;
    d * Real.sqrt 2, e, f * Real.sqrt 2;
    g, h * Real.sqrt 2, i]

def general_word_form_exits (x: GL (Fin 3) Real) (h: x ∈ G) :
  ∃ a b c d e f g h i, x = general_word_form a b c d e f g h i := by
    sorry


theorem case_one :∃ a b c : ℤ, ∃ n : ℕ, rotate 1 zero_one_zero = a_b_c_vec a b c n := by
    rw [rotate]
    use 0
    use 1
    use 0
    use 0
    rw [a_b_c_vec]
    simp
    rw [zero_one_zero]

  theorem case_gl_one : ∃ a b c : ℤ, ∃ n : ℕ, rotate gl_one zero_one_zero = a_b_c_vec a b c n := by
    rw [rotate]
    use 0
    use 1
    use 0
    use 0
    rw [a_b_c_vec]
    simp
    rw [zero_one_zero]
    rw [coe_gl_one_eq_one]
    simp

theorem case_a (x) (h: x = gl_a): ∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n := by
    rw [h]
    rw [rotate]
    rw [zero_one_zero]
    rw [coe_gl_a_eq_matrix_a]
    rw [matrix_a]
    use 0
    use 1
    use -2
    use 1
    rw [a_b_c_vec]
    simp
    norm_num


theorem case_b (x) (h: x = gl_b): ∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n := by
    rw [h]
    rw [rotate]
    rw [coe_gl_b_eq_matrix_b]
    rw [zero_one_zero]
    rw [matrix_b]
    use 2
    use 1
    use 0
    use 1
    rw [a_b_c_vec]
    simp
    norm_num


theorem hk (x : GL (Fin 3) Real) (h: x ∈ erzeuger): ∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n := by
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
theorem h_one : ∃ a b c : ℤ, ∃ n : ℕ, rotate G_one zero_one_zero = a_b_c_vec a b c n := by
  apply case_one

theorem vec_mul_abc_eq_abc (x : GL (Fin 3) Real)
  (h: ∃ j k l : ℤ, ∃ i : ℕ, rotate x zero_one_zero = a_b_c_vec j k l i) (a b c : ℤ) (n : Nat) :
  ∃ e f g : ℤ , ∃ m : Nat, Matrix.vecMul (a_b_c_vec a b c n) x = a_b_c_vec e f g m := by
  rw [a_b_c_vec]
  rw [← Matrix.vecMulᵣ_eq]
  rw [Matrix.vecMulᵣ]
  simp_rw [Matrix.transpose]




theorem h_mul (x y : GL (Fin 3) Real) (h1:∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n)
(h2 :∃ d e f : ℤ, ∃ m : ℕ, rotate y zero_one_zero = a_b_c_vec d e f m) :
∃ g h i : ℤ, ∃ o : ℕ, rotate (x*y) zero_one_zero = a_b_c_vec g h i o := by
  rw [rotate]
  rw [@Matrix.GeneralLinearGroup.coe_mul]
  rw [zero_one_zero]

  rw [rotate] at h1
  rw [zero_one_zero] at h1

  rw [rotate] at h2
  rw [zero_one_zero] at h2

  rcases h1 with ⟨a, b, c, n, h1'⟩
  rcases h2 with ⟨e, f, g, m, h2'⟩
  rw [← @Matrix.vecMul_vecMul]
  rw [h1']
  apply vec_mul_abc_eq_abc
  rw [rotate]
  rw [zero_one_zero]
  rw [h2']
  use e
  use f
  use g
  use m


def h_inv (x) (h1:∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n) :
  ∃ a b c n, rotate (x⁻¹) zero_one_zero = a_b_c_vec a b c n := by
  rw [rotate]
  rw [zero_one_zero]

  rw [rotate] at h1
  rw [zero_one_zero] at h1

  rcases h1 with ⟨a, b, c, n, h1'⟩
  simp
  sorry


theorem lemma_3_1 (p: GL (Fin 3) Real) (h: p ∈ G):
       ∃ a b c : ℤ, ∃ n : ℕ, rotate p zero_one_zero = a_b_c_vec a b c n:=
  Subgroup.closure_induction h hk h_one h_mul h_inv

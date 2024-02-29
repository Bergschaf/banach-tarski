import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

import Mathlib.Data.Matrix.Reflection

import banach_tarski.Definitions

--import banach_tarski.general_word_form

def coe_gl_one_eq_one : ↑gl_one = 1 := by
  exact Units.val_eq_one.mp rfl

def coe_gl_a_eq_matrix_a : ↑gl_a = matrix_a := by
  rfl

def coe_gl_b_eq_matrix_b : ↑gl_b = matrix_b := by
  rfl


noncomputable def a_b_c_vec (a b c : ℤ) (n : Nat) : r_3 :=
   ![1/3^n * a * Real.sqrt 2,1/3^n * b,1/3^n * c * Real.sqrt 2]

theorem x_inv_in_g (x: GL (Fin 3) Real) (h: x ∈ G): x⁻¹ ∈ G := by
  exact Subgroup.inv_mem G h



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


def G_one : G := 1
theorem h_one : ∃ a b c : ℤ, ∃ n : ℕ, rotate G_one zero_one_zero = a_b_c_vec a b c n := by
  apply case_one


variable (x : G_List)

lemma rotate_mul (p1 p2 : GL (Fin 3) Real) (i : r_3) : rotate (p1 * p2) i = rotate p1 (rotate p2 i) := by
  simp [rotate]

lemma rotate_preserve_gl_a {n : Nat} (i : r_3) (h : ∃ a b c : ℤ, ∃ n, i = a_b_c_vec a b c n) :
  ∃ a1 b1 c1 : ℤ , rotate gl_a i = a_b_c_vec a1 b1 c1 (n+1) := by
  simp [rotate]
  rw [coe_gl_a_eq_matrix_a]



  /--
  rcases h with ⟨a, b, c, n, h_r⟩
  rw [h_r]
  simp [matrix_a, a_b_c_vec]
  use a
  use b
  use c
  ext hi
  fin_cases hi
  simp-/




theorem lemma_3_1 {n : Nat} (p : List (erzeuger_t × Bool))  (h: List.length p = n):
  ∃ a b c : ℤ, rotate (list_to_matrix p) zero_one_zero = a_b_c_vec a b c n := by

    induction p with
    | nil =>
      use 0
      use 1
      use 0
      rw [list_to_matrix]
      rw [rotate]
      rw [coe_gl_one_eq_one]
      simp [zero_one_zero, a_b_c_vec]
      rw [← h]
      simp

    | cons head tail ih =>
      cases head with
      | mk fst snd =>
        cases fst
        cases snd
        simp [item_to_matrix,list_to_matrix, rotate_mul]







        sorry









/-
      simp
      use 0
      use 1
      use 0
      have h_empty : p = [] := by
        exact List.length_eq_zero.mp h
      rw [h_empty]
      rw [list_to_matrix]
      rw [rotate]
      rw [coe_gl_one_eq_one]
      simp [zero_one_zero, a_b_c_vec]
    | succ n ih =>
      sorry--/

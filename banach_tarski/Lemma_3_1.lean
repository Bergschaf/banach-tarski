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

import banach_tarski.general_word_form

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

theorem general_word_form_abc (a b c d e f g h i: ℤ) (n : Nat):
  ∃ l m o p, Matrix.vecMul zero_one_zero (general_word_form a b c d e f g h i n) =
    a_b_c_vec l m o p := by
    rw [general_word_form]
    use d
    use e
    use f
    use n
    rw [a_b_c_vec]
    rw [zero_one_zero]

    ext h1
    fin_cases h1
    simp
    ring

    simp
    ring

    simp
    ring




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

theorem vec_mul_abc_eq_abc (x : GL (Fin 3) Real) (h1: x ∈ G)
  (h: ∃ j k l : ℤ, ∃ i : ℕ, rotate x zero_one_zero = a_b_c_vec j k l i) (a b c : ℤ) (n : Nat) :
  ∃ e f g : ℤ , ∃ m : Nat, Matrix.vecMul (a_b_c_vec a b c n) x = a_b_c_vec e f g m := by
  rw [a_b_c_vec]
  rcases general_word_form_exists x h1 with ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1,n1, h2⟩
  rw [h2]
  rw [general_word_form]
  simp
  use a * a1 + b * d1 + c * g1
  use a * b1 * 2 + c * h1 * 2 + b * e1
  use  a * c1 + b * f1 + c * i1
  use n + n1
  rw [a_b_c_vec]
  ext hx
  fin_cases hx

  simp
  ring

  simp
  ring!
  simp
  norm_num
  ring
  norm_num
  ring


theorem h_mul (x : GL (Fin 3) Real) (hx: x ∈ G) (y: GL (Fin 3) Real) (hy: y ∈ G) (h1:∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n)
(h2 :∃ d e f : ℤ, ∃ m : ℕ, rotate y zero_one_zero = a_b_c_vec d e f m):
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

  apply hy

  rw [rotate]
  rw [zero_one_zero]
  rw [h2']
  use e
  use f
  use g
  use m


def h_inv (x : GL (Fin 3) Real) (hx: x ∈ G)  (h1:∃ a b c : ℤ, ∃ n : ℕ, rotate x zero_one_zero = a_b_c_vec a b c n):
  ∃ a b c n, rotate (x⁻¹) zero_one_zero = a_b_c_vec a b c n := by

  rw [rotate]
  rw [zero_one_zero]

  rw [rotate] at h1
  rw [zero_one_zero] at h1

  rcases h1 with ⟨a, b, c, n, h1'⟩
  simp

  rcases general_word_form_exists (x)⁻¹ (x_inv_in_g x hx) with ⟨a1, b1, c1, d1, e1, f1, g1,hh1,  i1, n1, h2⟩

  rw [← @Matrix.coe_units_inv]

  rw [h2]

  apply general_word_form_abc


theorem h_s (x : GL (Fin 3) Real) (h : x ∈ erzeuger) :
   ∃ a b c n, rotate x zero_one_zero = a_b_c_vec a b c n := by
    cases h with
    | inl ha =>
    apply case_a
    exact ha
    | inr hb =>
      apply case_b
      exact hb


theorem lemma_3_1 (p: GL (Fin 3) Real) (h: p ∈ G):
       ∃ a b c : ℤ, ∃ n : ℕ, rotate p zero_one_zero = a_b_c_vec a b c n:=
  Subgroup.closure_induction' h_s h_one h_mul h_inv h

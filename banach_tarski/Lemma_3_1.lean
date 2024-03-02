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

lemma coe_gl_one_eq_one : ↑gl_one = 1 := by
  exact Units.val_eq_one.mp rfl

lemma coe_gl_a_eq_matrix_a : ↑gl_a = matrix_a := by
  rfl

lemma coe_gl_a_inv_eq_matrix_a_inv : ↑gl_a' = matrix_a' := by
  rfl

lemma coe_gl_b_eq_matrix_b : ↑gl_b = matrix_b := by
  rfl

lemma coe_gl_b_inv_eq_matrix_b_inv : ↑gl_b' = matrix_b' := by
  rfl

noncomputable def a_b_c_vec (a b c : ℤ) (n : Nat) : r_3 :=
   ![1/3^n * a * Real.sqrt 2,1/3^n * b,1/3^n * c * Real.sqrt 2]


lemma rotate_mul (p1 p2 : GL (Fin 3) Real) (i : r_3) : rotate (p1 * p2) i = rotate p2 (rotate p1 i) := by
  simp [rotate]


lemma rotate_preserve_gl_a (n1 : Nat) (a1 b1 c1 : ℤ)  (i : r_3) (h : i = a_b_c_vec a1 b1 c1 n1) :
  rotate gl_a i = a_b_c_vec (3 * a1) (b1 + 4 * c1) (-2 * b1 + c1) (n1+1) := by
  simp [rotate]
  rw [coe_gl_a_eq_matrix_a]
  rw [h]
  simp [matrix_a, a_b_c_vec]

    -- TODO die werte hinter abc_vec anders als im Paper evtl FEHLER im paper
    -- TODO schon wieder anders
  ext hi
  fin_cases hi
  . simp
    left
    ring
  . simp
    ring
    rw [Real.sq_sqrt]
    simp
    ring
    norm_num
  . simp
    ring_nf

lemma rotate_preserve_gl_a' (n1 : Nat) (a1 b1 c1 : ℤ)  (i : r_3) (h : i = a_b_c_vec a1 b1 c1 n1) :
  rotate gl_a' i = a_b_c_vec (3 * a1) (b1 - 4 * c1) (2 * b1 + c1) (n1+1) := by
  simp [rotate]
  rw [coe_gl_a_inv_eq_matrix_a_inv]
  rw [h]
  simp [matrix_a', a_b_c_vec]

    -- TODO die werte hinter abc_vec anders als im Paper evtl FEHLER im paper
    -- TODO schon wieder anders
  ext hi
  fin_cases hi
  . simp
    left
    ring
  . simp
    ring
    rw [Real.sq_sqrt]
    simp
    ring
    norm_num
  . simp
    ring_nf

lemma rotate_preserve_gl_b (n1 : Nat) (a1 b1 c1 : ℤ)  (i : r_3) (h : i = a_b_c_vec a1 b1 c1 n1) :
  rotate gl_b i = a_b_c_vec (a1 + 2 * b1) (-4 * a1 + b1) (3 * c1) (n1+1) := by
  simp [rotate]
  rw [coe_gl_b_eq_matrix_b]
  rw [h]
  simp [matrix_b, a_b_c_vec]

    -- TODO die werte hinter abc_vec anders als im Paper evtl FEHLER im paper
    -- TODO schon wieder anders
  ext hi
  fin_cases hi
  . simp
    ring
  . simp
    ring
    rw [Real.sq_sqrt]
    simp
    ring
    norm_num
  . simp
    left
    ring_nf

lemma rotate_preserve_gl_b' (n1 : Nat) (a1 b1 c1 : ℤ)  (i : r_3) (h : i = a_b_c_vec a1 b1 c1 n1) :
  rotate gl_b' i = a_b_c_vec (a1 - 2 * b1) (4 * a1 + b1) (3 * c1) (n1+1) := by
  simp [rotate]
  rw [coe_gl_b_inv_eq_matrix_b_inv]
  rw [h]
  simp [matrix_b', a_b_c_vec]

    -- TODO die werte hinter abc_vec anders als im Paper evtl FEHLER im paper
    -- TODO schon wieder anders
  ext hi
  fin_cases hi
  . simp
    ring
  . simp
    ring
    rw [Real.sq_sqrt]
    simp
    ring
    norm_num
  . simp
    left
    ring_nf


theorem lemma_3_1 {n : Nat} (p : List (erzeuger_t × Bool))  (h: List.length p = n):
  ∃ a b c : ℤ, rotate (list_to_matrix p) zero_one_zero = a_b_c_vec a b c n := by
    induction p generalizing n with
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

    | cons head tail ih  =>
      cases n with
      | zero => cases h -- contradiction
      | succ d =>
          simp at h
          specialize @ih d h
          cases head with
          | mk fst snd =>
            rcases ih with ⟨a3, b3, c3, h3⟩
            simp [item_to_matrix,list_to_matrix, rotate_mul]
            rw [h3]
            cases fst
            . cases snd
              . rw [rotate_preserve_gl_a' d a3 b3 c3]
                use 3 * a3
                use b3 - 4 * c3
                use 2 * b3 + c3
                simp [rotate, a_b_c_vec]

              . rw [rotate_preserve_gl_a d a3 b3 c3]
                use 3 * a3
                use b3 + 4 * c3
                use -2 * b3 + c3
                simp [rotate, a_b_c_vec]

            . cases snd
              . rw [rotate_preserve_gl_b' d a3 b3 c3]
                use a3 - 2 * b3
                use 4 * a3 + b3
                use 3 * c3
                simp [rotate, a_b_c_vec]

              . rw [rotate_preserve_gl_b d a3 b3 c3]
                use a3 + 2 * b3
                use -4 * a3 + b3
                use 3 * c3
                simp [rotate, a_b_c_vec]

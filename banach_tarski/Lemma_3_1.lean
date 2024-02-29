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

def coe_gl_a_inv_eq_matrix_a_inv : ↑gl_a' = matrix_a' := by
  rfl

def coe_gl_b_eq_matrix_b : ↑gl_b = matrix_b := by
  rfl

def coe_gl_b_inv_eq_matrix_b_inv : ↑gl_b' = matrix_b' := by
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

/--
lemma rotate_preserve_abc_vec (a b c : ℤ ) (n : ℕ) (p : List (erzeuger_t × Bool)) (h1 :∃ a2 b2 c2 : ℤ, rotate (list_to_matrix p) zero_one_zero = a_b_c_vec a2 b2 c2 p.length):
    ∃ a1 b1 c1 : ℤ, rotate (list_to_matrix p) (a_b_c_vec a b c n) = a_b_c_vec a1 b1 c1 (n + p.length) := by
    induction p generalizing n with
    | nil =>
      simp [rotate, a_b_c_vec,list_to_matrix, coe_gl_one_eq_one]
      use a
      use b
      use c

    | cons head tail ih  =>
      simp at ih
      rcases h1 with ⟨a2, b2, c2, h2⟩
      cases head with
      | mk fst snd =>
        cases fst
        cases snd
        simp
        simp [list_to_matrix, item_to_matrix, rotate_mul]





      have h2_tail : rotate (list_to_matrix tail) zero_one_zero =
          a_b_c_vec a2 b2 c2 (List.length tail) := by
          sorry

      --apply (ih a2 b2 c2 h2_tail)
      sorry-/



lemma zero_one_zero_abc_form : zero_one_zero = a_b_c_vec 0 1 0 0 := by
  simp [zero_one_zero, a_b_c_vec]


-- TODO p is the wrong way (or rotate is...) check consistency with paper
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
            cases fst
            . cases snd
              . simp [item_to_matrix,list_to_matrix, rotate_mul]
                sorry
              . simp [item_to_matrix,list_to_matrix, rotate_mul]
                --rcases ih with ⟨a1, b1, c1, h1⟩
                have ih_2 : ∃ a b c, rotate (list_to_matrix tail) zero_one_zero = a_b_c_vec a b c d := by
                  apply ih

                rw [← h] at ih
                rcases ih_2 with ⟨a3, b3, c3, h3⟩
                --rw [← h]



                rw [rotate_preserve_gl_a 0 0 1 0 zero_one_zero zero_one_zero_abc_form]
                simp

                rw [← h]
                rw [Nat.succ_eq_add_one]
                rw [add_comm]



                --apply (rotate_preserve_abc_vec 0 1 (-2) 1 tail ih)

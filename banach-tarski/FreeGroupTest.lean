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

set_option maxHeartbeats 2000000
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
def x : ℚ := 5/3
def y : ℚ := 3
#eval x

abbrev matrix_3x3_q := Matrix (Fin 3) (Fin 3) ℚ

def matrix_a : matrix_3x3_q := !![3/5, -4/5, 0; 4/5, 3/5,0; 0, 0, 1]
def matrix_a' : matrix_3x3_q := !![3/5, 4/5, 0; -4/5, 3/5, 0; 0, 0, 1]
def matrix_b : matrix_3x3_q:= !![1,0,0;0,3/5,-4/5;0, 4/5, 3/5]
def matrix_b' :matrix_3x3_q := !![1,0, 0;0, 3/5, 4/5; 0, -4/5, 3/5 ]
def matrix_one : matrix_3x3_q := !![1, 0, 0; 0, 1, 0; 0, 0, 1]
---def matritzen : Set (Matrix (Fin 3) (Fin 3) Real) := {matrix_a, matrix_b, matrix_a', matrix_b', matrix_one}


theorem matrix_inverse_a :  matrix_a * matrix_a' = matrix_one := by
    rw [matrix_a]
    rw [matrix_a']
    rw [matrix_one]
    norm_num

theorem matrix_inverse_b :  matrix_b * matrix_b' = matrix_one := by
    rw [matrix_b]
    rw [matrix_b']
    rw [matrix_one]
    norm_num


#eval matrix_a * matrix_a'
#eval matrix_b * matrix_b'


def matrix_ab : Set matrix_3x3_q := {matrix_a, matrix_b, matrix_a', matrix_b'}
abbrev ab_subtype :=  {w : matrix_3x3_q | w ∈ matrix_ab}


def G := Group matrix_ab

abbrev r_3 := Fin 3 -> ℚ

def zero_one_zero : r_3 := ![0,1,0]


def fold (word : List ab_subtype) : matrix_3x3_q :=
  List.foldl (fun matrix1 matrix2=> matrix1 * matrix2) 1 word

theorem fold_zero_eq_one (word : List ab_subtype) (h : word.length = 0) : fold word = 1 := by
  rw [fold]
  sorry

theorem fold_p_n (word: List ab_subtype) (n : Nat) (h: word.length = n) :
   ∃ w : ab_subtype, fold word = (fold (word.take (n - 1))) *  w := by
  rw [fold]
  rw [fold]
  simp
  rw [← h]
  sorry


def rotate (word : List ab_subtype) (vec : r_3) : r_3 :=
  (fold word).vecMul vec


def a_b_c_vec (a b c n : Nat) : r_3 :=
  (1/5)^n * ![4 * a, 3 * b, -4 * c]

theorem lemma_3_1 (p: List ab_subtype) (a b c: ℚ) (n : Nat) (h: n = p.length):
       ∃ a b c, rotate p zero_one_zero = a_b_c_vec a b c n:= by

  induction n with
    | zero =>
    rw [rotate]
    simp
    use 0
    use 1
    use 0
    rw [a_b_c_vec]
    simp
    rw [fold_zero_eq_one]
    rw [zero_one_zero]
    simp


    exact h

    | succ d hd =>
    rw [rotate]
    have hp: p.length=d+1 := by
      apply symm
      rw [← Nat.succ_eq_add_one]
      exact h
    apply?






---def matrix_group := {w: GL (Fin 3) Real | true}

theorem matritzen_in_GL : ∀ x ∈ matritzen, x ∈ matrix_group :=
  sorry

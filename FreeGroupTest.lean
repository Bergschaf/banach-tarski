import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
set_option maxHeartbeats 20000

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


theorem union_f2 : s_a ∪ s_b ∪ s_a' ∪ s_b' ∪ e = f2 := by
  apply subset_antisymm
  intro x h
  sorry
  sorry



---theorem s_a_in_FreeGroup (s := s_a) (w : FreeGroup Generators) : (FreeGroup.toWord w).head? = (Generators.a, true) -> w ∈ s_a :=

---  sorry

--------------------

--def r_3_set := Set r_3

noncomputable def matrix_a : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,-2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
noncomputable def matrix_a' : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3,2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
noncomputable def matrix_b : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0;( 2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
noncomputable def matrix_b' :Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0;( -2/3*Real.sqrt 2),1/3, 0; 0, 0, 1]
noncomputable def matrix_one : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1, 0; 0, 0, 1]

noncomputable def matritzen : Set (Matrix (Fin 3) (Fin 3) Real) := {matrix_a, matrix_b, matrix_a', matrix_b', matrix_one}

def r_3 := Matrix (Fin 3) (Fin 1) Real

def rotate (matrix : Matrix (Fin 3) (Fin 3) Real) (vec : r_3) : r_3 :=
  vec


theorem lemma_3_1 (p: r_3 -> r_3):true := by

  sorry

def matrix_group := {w: Group matritzen | true}

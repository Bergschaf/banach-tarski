import Mathlib.Tactic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup


inductive Generators where
  | a : Generators
  | b : Generators
  deriving DecidableEq
open Generators
--theorem: FreeGroup.toWord_one{α : Type u} [DecidableEq α] :
--  FreeGroup.toWord 1 = []
def f2 := {w: FreeGroup Generators | true}
def e := {w: FreeGroup Generators | (FreeGroup.toWord w) = []}
def s_a := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.a, true)}
def s_b := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.b, true)}
def s_a' := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.a, false)}
def s_b' := {w : FreeGroup Generators  | (FreeGroup.toWord w).head? = .some (Generators.b, false)}

#check s_a
#check e


theorem about_s_a (z : FreeGroup Generators) : z ∈ s_a -> ((FreeGroup.toWord z).head? = .some (Generators.a, true)) := by
  intro x
  use x
#check f2

theorem s_a_in_f2 : x ∈ s_a -> x ∈ f2 := by
  intro h


theorem union_f2 : s_a ∪ s_b ∪ s_a' ∪ s_b' ∪ e = f2 := by
  apply subset_antisymm
  intro x h
  cases' h with h1 h2
  cases' h1 with h3 h4
  cases' h3 with h5 h6
  cases' h5 with h7 h8



---theorem s_a_in_FreeGroup (s := s_a) (w : FreeGroup Generators) : (FreeGroup.toWord w).head? = (Generators.a, true) -> w ∈ s_a :=

---  sorry

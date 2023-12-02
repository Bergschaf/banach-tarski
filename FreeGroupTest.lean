import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup


inductive Generators where
  | a : Generators
  | b : Generators
  deriving DecidableEq
open Generators



def s_a := {w : FreeGroup Generators  // (FreeGroup.toWord w).head? = (Generators.a, true)}
def s_b := {w : FreeGroup Generators  // (FreeGroup.toWord w).head? = (Generators.b, true)}
def s_a' := {w : FreeGroup Generators  // (FreeGroup.toWord w).head? = (Generators.a, false)}
def s_b' := {w : FreeGroup Generators  // (FreeGroup.toWord w).head? = (Generators.b, false)}

#check s_a

--theorem about_s_a (s_a) : (s_a ≠ { }) where
--  sorry

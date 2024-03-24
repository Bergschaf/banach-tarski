import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

import LeanCopilot

def sum_up_to (n : Nat): ℕ :=
  match n with
    | 0 => 0
    | (Nat.succ n) => sum_up_to n + Nat.succ n

#eval sum_up_to 10

theorem kleiner_gauss (n: Nat) :
  sum_up_to n * 2 = n * (n + 1) := by
  

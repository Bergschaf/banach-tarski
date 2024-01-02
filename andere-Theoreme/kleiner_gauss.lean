import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

def sum_up_to (n : Nat): ℕ :=
  match n with
    | 0 => 0
    | (Nat.succ n) => sum_up_to n + Nat.succ n

#eval sum_up_to 4



theorem kleiner_gauss (n: Nat) :
  sum_up_to n * 2 = n * (n + 1) := by

  induction n with
    | zero =>
      simp

    | succ d hd =>
    rw [sum_up_to]
    rw [Nat.succ_eq_add_one]
    rw [Nat.add_mul]
    rw [Nat.mul_add]
    rw [Nat.mul_one]

    rw [Nat.add_mul d 1 (d + 1)]
    simp
    rw [add_assoc]
    rw [← Nat.mul_two (d + 1)]
    simp
    use hd

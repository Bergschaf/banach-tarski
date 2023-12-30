import Mathlib.Data.Real.Basic

structure complex where
  re : Real
  im : Real

instance : Zero complex :=
    ⟨⟨0,0⟩⟩

instance : One complex :=
    ⟨⟨1,1⟩⟩


instance : Add complex :=
  ⟨ fun x y  ↦  ⟨ x.re + y.re, x.im + y.im ⟩ ⟩

instance : Neg.Add complex :=
  ⟨ fun x ↦ ⟨ -x.re, -x.im⟩ ⟩

instance : Mul complex :=
  ⟨ fun x y  ↦  ⟨ x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

instance : Neg.Mul complex :=
  ⟨ fun x  ↦  ⟨ x.re / (x.re^2+x.im^2), -x.im / (x.re^2+x.im^2)⟩⟩



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
    rw [sum_up_to]
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
    exact hd








  





  





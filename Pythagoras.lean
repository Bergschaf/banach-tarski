import Mathlib.Data.Real.Basic


structure complex where
  re : Real
  im : Real

instance : Zero complex :=
    ⟨⟨0,0⟩⟩

instance : One complex :=
    ⟨⟨1,1⟩⟩


instance : Add complex :=
  ⟨ fun x y  ↦   ⟨ x.re + y.re, x.im + y.im ⟩ ⟩

instance : Neg complex :=
  ⟨ fun x ↦ ⟨ -x.re, -x.im⟩ ⟩

instance : Mul complex :=
  ⟨fun x y  ↦   ⟨ x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

#check ∑ i in range 1, n
theorem kleiner_gauss (n i: Nat) : (∑ n in range 1, n) = n * (n + 1) / 2:=

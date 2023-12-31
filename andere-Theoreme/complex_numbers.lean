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

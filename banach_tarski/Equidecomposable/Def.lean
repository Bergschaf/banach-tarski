import Mathlib.Analysis.NormedSpace.AffineIsometry
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Logic.Function.Defs

universe u
variable (k : Type u)[NormedField k]
variable (V : Type u)[SeminormedAddCommGroup V][NormedSpace k V]
variable (P : Type u)[PseudoMetricSpace P][NormedAddTorsor V P]

def equidecomposable (B₁ B₂ : Set P) : Prop :=
  ∃ (P_B₁ : Finpartition B₁), ∃ (P_B₂ : Finpartition B₂), ∃ (f : P_B₁.parts → P_B₂.parts),
    P_B₂.parts.val.sizeOf = P_B₁.parts.val.sizeOf ∧
  Function.Bijective f ∧ (∀ p_b₁ : P_B₁.parts, ∃ (a : AffineIsometry k P P),
    ∀ x ∈ p_b₁.val, ∃ y ∈ (f p_b₁).val, a.toFun x = y ∧
    ∀ y ∈ (f p_b₁).val, ∃ x ∈ p_b₁.val, a.toFun x = y)

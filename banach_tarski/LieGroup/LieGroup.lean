import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic

class ConnectedLieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
   [ConnectedSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
   (I : ModelWithCorners 𝕜 E H) (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
   extends LieGroup I G


structure LieSubgroup  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] extends LieGroup I G where
      carrier : Set G
      mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
      one_mem' : 1 ∈ carrier
      inv_mem' : ∀ {x : G}, x ∈ carrier → x⁻¹ ∈ carrier


structure DenseLieSubgroup  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] extends LieSubgroup I G where
    dense : Dense carrier

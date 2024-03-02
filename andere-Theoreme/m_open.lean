import Mathlib.Topology.MetricSpace.Basic

variable {X : Type*} [MetricSpace X] (M : Set X)

-- Definition der Offenheit
def is_open_set (M : Set X) : Prop :=
  ∀ x ∈ M, ∃ ε > 0, Metric.ball x ε ⊆ M

-- Definition der Abgeschlossenheit
def is_closed_set (M : Set X) : Prop :=
  is_open_set Mᶜ

def is_accumulation_point (x : X) : Prop :=
  ∀ε > 0, ∃ y ∈ M, y ≠ x ∧ Dist.dist y x < ε


theorem closed_iff_complement_open (M : Set X) : is_closed_set M ↔ is_open_set Mᶜ := by
  rfl

theorem compl_compl_eq_set (M : Set x) : M = Mᶜᶜ := by
  exact eq_compl_comm.mpr rfl


-- Beweis, dass M offen ist, wenn und nur wenn Mᶜ abgeschlossen ist
theorem open_iff_complement_closed (M : Set X) :
  is_open_set M ↔ is_closed_set Mᶜ := by
  rw [iff_def]

  have h: is_open_set M -> is_closed_set Mᶜ := by
  intro h1 x
  rw [compl_compl]
  intro hx
  exact h1 x hx

  have k: is_closed_set Mᶜ -> is_open_set M
  intro k1 x
  rw [compl_compl_eq_set M]
  intro kx
  exact k1 x kx

  exact { left := h, right := k }

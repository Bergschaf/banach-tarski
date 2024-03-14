import banach_tarski.Definitions
import banach_tarski.Orbit

/--
TODO überprüfen ob Blueprint stimmt
ist X die Menge aller Elemente von M welche Ausschließlich aus Rotationen um A⁻¹ bestehen
ODER ist X die Menge aller Punkte die von M aus Ausschließlich durch Rotationen um A⁻¹ erreicht werden können
-/
def X : Set r_3 := {w : r_3 | ∃ x ∈ M, ∃ n : ℕ, rotate_n_times n gl_a' x = w}

def P₁ := rotate_set_around_set M S_A ∪ M ∪ X
def P₂ := rotate_set_around_set M S_A' \ X
def P₃ := rotate_set_around_set M S_B
def P₄ := rotate_set_around_set M S_B'

/--
Benötigt eigenschaften der Startpunkte
--/
lemma union_parts : L' \ D = P₁ ∪ P₂ ∪ P₃ ∪ P₄ := by
  refine Set.ext ?h
  intro x
  apply Iff.intro
  --
  intro h1
  by_cases h2:(x ∈ P₁)
  . exact Or.inl (Or.inl (Or.inl h2))
  --
  by_cases h3:(x ∈ P₃)
  . apply Or.inl
    apply Or.inr
    exact h3
  --
  by_cases h4:(x ∈ P₂)
  . apply Or.inl
    apply Or.inl
    apply Or.inr
    exact h4
  --
  apply Or.inr
  simp [P₁, P₂, P₃, P₄] at *
  sorry
  --
  intro h
  sorry

lemma rot_A_P₂ : rotate_set P₂ gl_a = P₂ ∪ P₃ ∪ P₄ := by
  simp [rotate_set, rotate, P₁, P₂, P₃, P₄]
  ext x1
  apply Iff.intro
  intro h
  rcases h with ⟨x2,⟨h1,h3⟩,h2⟩
  simp [rotate_set_around_set, rotate] at h1
  rcases h1 with ⟨rot_list, ⟨h_rot_reduced, h_rot_list⟩ , m, h_m, h1⟩
  sorry

  save
  intro h
  rcases h with ⟨h1, h2⟩
  repeat sorry

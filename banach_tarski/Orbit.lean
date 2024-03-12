import banach_tarski.Lemma_3_1
import banach_tarski.Definitions
--import banach_tarski.Equidecomposable


def same_orbit (a b: r_3) := ∃ p : G, rotate p a = b

def orbit_A (a : r_3) := {b: L | same_orbit a b}

def list_intersection_pairwise (α : Type) (w : List (Set α)) : Prop :=
    ∀ i j : Fin (w.length), i ≠ j -> w.get i ∩ w.get j = ∅

def all_orbits : Set (Set r_3) := {w : Set r_3 | ∃ x : L,(Set.Nonempty w) ∧  orbit_A x = w}

lemma all_orbits_countable : Set.Countable all_orbits := by sorry

noncomputable def choose (x : Set r_3) (hx: x ∈ all_orbits) : r_3 := Id.run do
    have h: ∃ a : r_3, a ∈ x := by
        rw [all_orbits] at hx
        refine Set.nonempty_def.mp ?_
        rcases hx with ⟨Fin.heq_ext_iff, b, _⟩
        exact b
    return Classical.choose h

def M : Set r_3 := {w : r_3 | ∃ x : Set  r_3, ∃ hx : (x ∈ all_orbits), choose x hx = w}

lemma M_countable : Set.Countable M := by sorry

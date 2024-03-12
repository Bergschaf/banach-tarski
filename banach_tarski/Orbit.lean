import banach_tarski.Lemma_3_1
import banach_tarski.Definitions
--import banach_tarski.Equidecomposable


def same_orbit (a b: r_3) := ∃ p : G, rotate p a = b

def orbit_A (a : r_3) := {b: L | same_orbit a b}

def list_intersection_pairwise (α : Type) (w : List (Set α)) : Prop :=
    ∀ i j : Fin (w.length), i ≠ j -> w.get i ∩ w.get j = ∅

def all_orbits : Set (Set r_3) := {w : Set r_3 | ∃ x : L,(Set.Nonempty w) ∧  orbit_A x = w}


--def all_orbits_list (punkte : Set r_3) : List (Set r_3) :=

noncomputable def rep_punkte (orbits : List (Set r_3)) (h_nonempty: ∀ x ∈ orbits, Set.Nonempty x): List r_3 :=
    match orbits with
    | [] => []
    | x::tail =>
        have h: ∃ a : r_3, a ∈ x := by
            exact h_nonempty x (List.Mem.head tail)

        have h_nonempty_new : ∀ x ∈ tail, Set.Nonempty x := by
            exact fun x_1 a ↦ h_nonempty x_1 (List.Mem.tail x a)

        (Classical.choose h)::(rep_punkte tail h_nonempty_new)

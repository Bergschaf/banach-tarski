import banach_tarski.Lemma_3_1
import banach_tarski.Definitions
import banach_tarski.Equidecomposable


def same_orbit (a b: r_3) := ∃ p : G, rotate p a = b

def orbit_A (a : r_3) := {b: L | same_orbit a b}

def list_intersection_pairwise (α : Type) (w : List (Set α)) : Prop :=
    ∀ i j : Fin (w.length), i ≠ j -> w.get i ∩ w.get j = ∅

#check list_intersection_pairwise


def all_orbits : Set (Set r_3) := {w : Set r_3 | ∃ x : L, orbit_A x = w}

/--
def L_list : List r_3 := [w : L]

def all_orbits_list : List (Set r_3) :=

lemma test : [1] = {1,1,1,1} := by
  exact rfl
--- -> ein Set kann keine duplizierten elemente enthalten

def rep_punkte : Set r_3 := Real.choose



lemma all_orbits_different : list_interesction_pairwise := by
  sorry


--def M := Real.choose-/

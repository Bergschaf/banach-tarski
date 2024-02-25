import banach_tarski.Lemma_3_1
import banach_tarski.Definitions

def same_orbit (a b: r_3) := ∃ p : G, rotate p a = b

def orbit_A (a : r_3) := {b: r_3 | same_orbit a b}

def all_orbits := List (orbit_A origin)

#check all_orbits

--def M := Real.choose

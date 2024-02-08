import banach_tarski.Lemma_3_1

def L := {x: r_3 | x ∈ Metric.ball 0 1}
def origin : r_3 := ![0,0,0]
def L' := L \ {origin}

def same_orbit (a b: r_3) := ∃ p : G, rotate p a = b

def orbit_A (a : r_3) := {b: r_3 | same_orbit a b}

def all_orbits := List (orbit_A origin)

#check all_orbits

--def M := Real.choose

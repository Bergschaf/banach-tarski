import banach_tarski.Definitions
import banach_tarski.Orbit

/--
TODO überprüfen ob Blueprint stimmt
ist X die Menge aller Elemente von M welche Ausschließlich aus Rotationen um A⁻¹ bestehen
ODER ist X die Menge aller Punkte die von M aus Ausschließlich durch Rotationen um A⁻¹ erreicht werden können
-/
def X : Set r_3 := {w : r_3 | ∃ x ∈ M, ∃ n : ℕ, rotate_n_times n gl_a' x = w}

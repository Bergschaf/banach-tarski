import banach_tarski.Lemma_3_1
#check rotate


theorem freeGroup (x: GL (Fin 3) Real) (h: x ∈ G) (n: Nat):
  rotate x zero_one_zero = a_b_c_vec 0 (3^n) 0 n -> n = 0 := by
    rw [zero_one_zero]

    intro h1

    rw [a_b_c_vec] at h1
    simp at h1
    
    
  
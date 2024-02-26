import banach_tarski.Lemma_3_1
#check rotate


theorem freeGroup (x: GL (Fin 3) Real) (h: x ∈ G) (n: Nat):
  rotate x zero_one_zero = a_b_c_vec 0 (3^n) 0 n -> n > 0 -> false := by
    rw [a_b_c_vec]


    rcases lemma_3_1 x h with ⟨a, b, c, nnn, h1⟩
    have h2 : nnn = n := by
      sorry
    rw [h1]
    simp
    rw [a_b_c_vec]
    rw [h2]
    simp
    ring_nf
    sorry



    -- TODO Funktioniert nicht, weil die Länge beliebig ist, in diesem fall muss
    -- TOOD länge eines wortes anhand der abc_form defnieren

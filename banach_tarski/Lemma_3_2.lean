import banach_tarski.Lemma_3_1
#check rotate


theorem freeGroup {n : ℕ} (p : List (erzeuger_t × Bool)) (hn : p.length = n):
  rotate (list_to_matrix p) zero_one_zero = zero_one_zero -> n = 0 := by
    rcases lemma_3_1 p hn with ⟨a, b, c, h3⟩
    rw [h3]
    simp [a_b_c_vec, zero_one_zero]
    sorry






    -- TODO Funktioniert nicht, weil die Länge beliebig ist, in diesem fall muss
    -- TOOD länge eines wortes anhand der abc_form defnieren

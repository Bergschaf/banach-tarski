import banach_tarski.Lemma_3_1
#check rotate

variable (n1 : Nat)

theorem freeGroup (x: GL (Fin 3) Real) (h: x ∈ G) (n: Nat) (h4 : n1 > 0):
  rotate x zero_one_zero = a_b_c_vec 0 (3^n) 0 n -> false := by
    rw [zero_one_zero]

    rw [a_b_c_vec]

    rw [rotate]

    --cases general_word_form_exists x h

    rcases general_word_form_exists x h with ⟨a1, b1, c1, d1, e1, f1, g1, h1, i1, n1, h2⟩

    rw [h2]

    rw [general_word_form]
    simp
    -- TODO Funktioniert nicht, weil die Länge beliebig ist, in diesem fall muss

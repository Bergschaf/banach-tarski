import banach_tarski.Lemma_3_1
#check rotate


theorem freeGroup {n : ℕ} (p : List (erzeuger_t × Bool)) (hn : p.length = n):
  rotate (list_to_matrix p) zero_one_zero = zero_one_zero -> n = 0 := by
    induction p generalizing n with
    | nil =>
      simp [rotate, zero_one_zero, list_to_matrix, coe_gl_one_eq_one]
      exact id hn.symm
    | cons head tail ih =>
      cases hn
      simp
      cases head with
      | mk fst snd =>
        cases fst
        cases snd
        . simp [list_to_matrix, zero_one_zero, item_to_matrix, coe_gl_a_inv_eq_matrix_a_inv]
          rw [rotate_mul]
          sorry
      simp at hn
      have hn_ : List.length tail = n - 1 := by
        exact eq_tsub_of_add_eq hn

      specialize @ih (n -1) hn_









    -- TODO Funktioniert nicht, weil die Länge beliebig ist, in diesem fall muss
    -- TOOD länge eines wortes anhand der abc_form defnieren

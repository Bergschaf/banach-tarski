import banach_tarski.Lemma_3_1

/- todo stimmt nicht -> es gibt nicht reduzierte List (erzeuger x bool)
-- theorem freeGroup {n : ℕ} (p : List (erzeuger_t × Bool)) (hn : p.length = n):
--   rotate (list_to_matrix p) zero_one_zero = zero_one_zero -> list_to_matrix p = gl_one := by
--     induction p generalizing n with
--     | nil =>
--       simp [rotate, zero_one_zero, list_to_matrix, coe_gl_one_eq_one]
--       exact id hn.symm
--     | cons head tail ih =>
--       cases hn
--       simp
--       cases head with
--       | mk fst snd =>
        cases fst
        cases snd
        . simp [list_to_matrix, zero_one_zero, item_to_matrix, coe_gl_a_inv_eq_matrix_a_inv]
          rw [rotate_mul]
          sorry
        . sorry
        sorry



    -- TODO Funktioniert nicht, weil die Länge beliebig ist, in diesem fall muss
    -- TOOD länge eines wortes anhand der abc_form defnieren-/

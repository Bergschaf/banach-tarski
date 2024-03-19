import banach_tarski.Definitions



lemma list_to_matrix_inj_FreeGroup_reduce (L₁ L₂ : List (erzeuger_t × Bool)) (h: FreeGroup.reduce L₁ = FreeGroup.reduce L₂) :
  list_to_matrix L₁ = list_to_matrix L₂ := by
  induction L₁ with
  | nil =>
    simp [list_to_matrix]
    sorry

  | cons head tail ih =>
    induction L₂ generalizing tail with
    | nil =>
      sorry
    | cons head1 tail1 ih1 =>
      sorry



lemma rotate_SA :
  ∀ x ∈ S_A, ∃ y ∈ S_B ∪ S_B' ∪ S_A, list_to_matrix ((erzeuger_t.gl_a, false)::x) = list_to_matrix y := by
    intro x hx
    sorry


lemma reduce_empty {α : Type} [DecidableEq α] (x : List (α × Bool)) (hx : x = []) :
  FreeGroup.reduce x = [] := by
  rename_i inst
  aesop_subst hx
  apply Eq.refl

lemma reduce_len_eq {α : Type} [DecidableEq α] (L : List (α × Bool)):
  L.length = (FreeGroup.reduce L).length ↔ FreeGroup.reduce L = L := by
    apply Iff.intro
    intro h
    induction L with
    | nil =>
      rename_i inst
      simp_all only [List.length_nil]
      apply Eq.refl
    | cons head tail ih =>
      simp
      sorry
    rename_i inst
    intro a
    simp_all only

lemma reduce_len {α : Type} [DecidableEq α] (L: List (α × Bool)) (x : α × Bool):
  (FreeGroup.reduce (x::L)).length ≤ 1 + (FreeGroup.reduce L).length := by
  simp
  sorry

variable {α : Type} [DecidableEq α] {x : List (α × Bool)}

lemma reduce_ne_inv_pair {L : List (α × Bool)} : FreeGroup.reduce x ≠ (a, b) :: (a, !b) :: L := by
  have : (a, b) :: (a, !b) :: L = [] ++ (a, b) :: (a, !b) :: L := by rw [List.nil_append]
  rw [this]
  exact FreeGroup.reduce.not

lemma tail_reduced_eq_reduced (hx : x = FreeGroup.reduce x)
  : x.tail = FreeGroup.reduce x.tail := by
  cases x with
  | nil => exact hx
  | cons head tail =>
    rw [FreeGroup.reduce.cons] at hx
    by_cases h1 : FreeGroup.reduce tail = []
    · simp [h1] at hx
      simp [hx, FreeGroup.reduce]
    · obtain ⟨b, L, h2⟩ := List.exists_cons_of_ne_nil h1
      simp only [h2] at hx
      split_ifs at hx with h3
      · cases b; cases head
        simp only at h3
        cases' h3 with h4 h5
        rw [← hx, h4, h5] at h2
        exact (reduce_ne_inv_pair h2).elim
      · rw [List.cons_inj] at hx
        rw [List.tail_cons, h2]
        exact hx


lemma rotate_back_S_A (start : Set r_3) :
    rotate_set (rotate_set_around_set start S_A) gl_a' =
    (rotate_set_around_set start S_A) ∪ (rotate_set_around_set start S_B)
    ∪ (rotate_set_around_set start S_B') := by
    ext x1
    apply Iff.intro
    intro h1
    simp
    by_cases hc1:(x1 ∈ rotate_set_around_set start S_A)
    .  exact Or.inl (Or.inl hc1)
    --
    by_cases hc2:(x1 ∈ rotate_set_around_set start S_B')
    .  exact Or.inr hc2
    --
    left
    right
    simp [rotate_set_around_set, rotate] at h1
    rcases h1 with ⟨x2,⟨rot, ⟨h_rot_reduced, rot_in_S_A⟩ , x_start, ⟨hx_start, h_start_mul⟩⟩,h1⟩

    simp [rotate_set_around_set, rotate]
    use rot.tail
    apply And.intro
    . --use (tail_reduced_eq_reduced rot h_rot_reduced)
      sorry
    . sorry

    ---
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        sorry
      | inr h =>
        sorry

    | inr h =>
      simp [rotate_set_around_set, rotate_set, rotate] at *
      rcases h with ⟨rot, ⟨h_rot_reduced, h_rot_in_SB⟩, x2, hx2_in_start, hx2_2⟩
      sorry


lemma SA_tail :
  ∀ x ∈ S_A, ∃ y ∈ S_B ∪ S_B' ∪ S_A, x.val ≠ [] -> x.val.tail = y := by
    intro x hx
    simp
    use x.val.tail
    simp [tail_reduced_eq_reduced]
    have h : List.tail x = FreeGroup.reduce (List.tail x.val) := by
      simp [S_A, G_list] at x
      apply tail_reduced_eq_reduced
      apply x.property
    use h
    sorry

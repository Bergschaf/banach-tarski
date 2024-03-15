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

lemma tail_reduced_eq_reduced {α : Type} [DecidableEq α] (L : List (α × Bool)) (x : α × Bool) (h: FreeGroup.reduce (x::L) = x::L) :
  FreeGroup.reduce L = L := by
  rw [← reduce_len_eq] at *
  sorry

lemma tail_reduced_eq_reduced_ {α : Type} [DecidableEq α] (L : List (α × Bool)) (x : α × Bool) (h: FreeGroup.reduce L = L) :
  L.tail = FreeGroup.reduce L.tail := by
  sorry


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
  ∀ x ∈ S_A, ∃ y ∈ S_B ∪ S_B' ∪ S_A,x.val ≠ [] -> x.val.tail = y := by
    intro x hx
    simp
    use x.val.tail
    simp [tail_reduced_eq_reduced]
    have h : List.tail x = FreeGroup.reduce (List.tail x.val) := by
      simp [S_A, G_list] at x
      apply tail_reduced_eq_reduced_
      use erzeuger_t.gl_a -- why??
      use true -- why???
      symm
      apply x.property

    use h
    sorry

--lemma S_A_tail :
--  ∀ x ∈ S_A, List.tail x ∈ S_B ∪ S_B' ∪ S_A := by
--  sorry

import banach_tarski.Definitions

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
    use (erzeuger_t.gl_a,false)::rot
    repeat sorry

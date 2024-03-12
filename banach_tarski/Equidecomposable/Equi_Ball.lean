import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Equi_Kreis

---- TODO kreis nicht mit weirder formel sondern mit funktion die den normalen kreis verschiebt und skaliert
--- -> beweis dass ein verschobenener Kreis immnernoch equidekomponierbar ist
def Kreis_in_Kugel : Set r_3 := {p : r_3 | ((2 * (p 0) - 1)) ^ 2 + (2 * (p 1)) ^ 2 = 1 ∧ p 2 = 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1}
def Kreis_in_Kugel_ohne_Origin : Set r_3 := Kreis_in_Kugel \ {origin}

def BB := L \ Kreis_in_Kugel

def Kreis_in_Kugel_A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![1/2 * Real.cos (n * sq_2) + 1/2,1/2 * Real.sin (n * sq_2),0]} -- TODO
def Kreis_in_Kugel_B := Kreis_in_Kugel \ Kreis_in_Kugel_A


lemma Kreis_subset_L : BB ∪ Kreis_in_Kugel = L := by
  simp [Kreis_in_Kugel, L, BB]
  intro x h1 h2 h3 h4
  simp [h2]
  rw [← h1]
  ring_nf
  rw [← h1]
  ring_nf
  repeat rw [sq] at h1
  ring_nf at h1
  apply_fun (. - 1) at h1
  ring_nf at h1
  apply_fun (. + ((x 0 * 4)- x 0 ^ 2 * 4)) at h1
  ring_nf at h1
  apply_fun (. * 4⁻¹) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3

lemma BB_Kreis_in_Kugel_no_intersection  : BB ∩ Kreis_in_Kugel = ∅ := by
  simp [BB, Kreis_in_Kugel]

lemma union_div_trans {α : Type} (a b c : Set α) (ha : b ⊆ a) (hb : c ⊆ b): a \ b ∪ b \ c = a \ c := by
  refine Set.ext_iff.mpr ?_
  intro x
  apply Iff.intro
  . simp
    intro h
    cases h with
    | inl h =>
      apply And.intro
      . exact Set.mem_of_mem_diff h
      . apply Set.not_mem_subset hb
        exact Set.not_mem_of_mem_diff h
    | inr h =>
      apply And.intro
      . unhygienic with_reducible aesop_destruct_products
        apply ha
        simp_all only
      . exact Set.not_mem_of_mem_diff h
  . intro h1
    simp
    by_cases h2:(x ∈ b)
    . right
      apply And.intro
      . exact h2
      . exact Set.not_mem_of_mem_diff h1
    . left
      apply And.intro
      . exact Set.mem_of_mem_diff h1
      . exact h2


lemma BB_and_Kreis_in_Kugel_ohne_origin_eq_L' : BB ∪ Kreis_in_Kugel_ohne_Origin = L' := by
  simp [BB, Kreis_in_Kugel_ohne_Origin, L']--, Kreis_in_Kugel, origin, L', L]
  apply union_div_trans
  simp [Kreis_in_Kugel, L]
  intro x h1 h2 h3 h4
  simp [h2]
  rw [← h1]
  ring_nf
  rw [← h1]
  ring_nf
  repeat rw [sq] at h1
  ring_nf at h1
  apply_fun (. - 1) at h1
  ring_nf at h1
  apply_fun (. + ((x 0 * 4)- x 0 ^ 2 * 4)) at h1
  ring_nf at h1
  apply_fun (. * 4⁻¹) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3
  --
  simp [origin, Kreis_in_Kugel]

lemma intersection_BB_Kreis_in_Kugel_ohne_Origin_eq_nil : BB ∩ Kreis_in_Kugel_ohne_Origin = ∅ := by
  simp [BB, Kreis_in_Kugel_ohne_Origin]
  refine Set.ext ?h
  intro x
  simp
  intro h1 h2 h3
  exfalso
  contradiction


lemma union_A_B_eq_Kreis : list_union r_3 [Kreis_in_Kugel_A, Kreis_in_Kugel_B] = Kreis_in_Kugel := by
  simp [list_union, union, Kreis_in_Kugel_A, Kreis_in_Kugel_B, Kreis_in_Kugel]
  intro a n h1 h2
  apply And.intro
  . aesop
    ring_nf
    simp_all only [Real.cos_sq_add_sin_sq]
  . apply And.intro
    . simp [h2]
    . simp [h2]
      apply And.intro
      . rw [← @le_sub_iff_add_le]
        norm_num
        apply Real.cos_le_one
      . rw [mul_comm]
        apply mul_le_one
        apply Real.sin_le_one
        norm_num
        norm_num


lemma equi_kugel_ohne_origin : equidecomposable Kreis_in_Kugel Kreis_in_Kugel_ohne_Origin := by
  rw [equidecomposable]
  use [Kreis_in_Kugel_A, Kreis_in_Kugel_B]
  simp
  apply And.intro
  . simp [list_intersection, list_union, union, pairs, intersection, Kreis_in_Kugel_A, Kreis_in_Kugel_B]
  . apply And.intro
    . exact union_A_B_eq_Kreis
    . use [gl_sq_2, gl_one]
      sorry



theorem equi_kugel : equidecomposable L L' := by
  apply equidecomposable_subset L L' BB Kreis_in_Kugel BB Kreis_in_Kugel_ohne_Origin
  --
  exact Kreis_subset_L
  --
  exact BB_Kreis_in_Kugel_no_intersection
  --
  exact BB_and_Kreis_in_Kugel_ohne_origin_eq_L'
  --
  exact intersection_BB_Kreis_in_Kugel_ohne_Origin_eq_nil
  --
  rfl
  --
  exact equi_kugel_ohne_origin

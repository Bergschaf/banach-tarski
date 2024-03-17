import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Equi_Kreis

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex


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

---- TODO kreis nicht mit weirder formel sondern mit funktion die den normalen kreis verschiebt und skaliert
--- -> beweis dass ein verschobenener Kreis immnernoch equidekomponierbar ist
def Kreis_in_Kugel : Set r_3 := {p : r_3 | ((2 * (p 0) - 1)) ^ 2 + (2 * (p 1)) ^ 2 = 1 ∧ p 2 = 0 ∧ p 0 ≤ 1}
def Kreis_in_Kugel_ohne_Origin : Set r_3 := Kreis_in_Kugel \ {origin}

def BB := L' \ Kreis_in_Kugel_ohne_Origin

def Kreis_in_Kugel_A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![1/2 * Real.cos (n * sq_2) + 1/2,1/2 * Real.sin (n * sq_2),0]} -- TODO
def Kreis_in_Kugel_B := Kreis_in_Kugel_ohne_Origin \ Kreis_in_Kugel_A

lemma Kreis_subset_L : Kreis_in_Kugel ⊆ L := by
  simp [Kreis_in_Kugel,L]
  intro a h1 h2 h3
  rw [h2]
  simp
  apply_fun (. - (2 * a 0 - 1) ^ 2) at h1
  ring_nf at h1
  apply_fun (. / 4) at h1
  ring_nf at h1
  rw [h1]
  simp
  exact h3

lemma BB_union_Kreis_in_Kugel_eq_L : BB ∪ Kreis_in_Kugel = L := by
  simp [BB, L', Kreis_in_Kugel_ohne_Origin]
  rw [Set.diff_diff]
  rw [Set.union_diff_cancel]
  simp only [Set.diff_union_self, Set.union_eq_left]

  exact Kreis_subset_L

  simp [origin, Kreis_in_Kugel]
  


lemma BB_and_Kreis_in_Kugel_ohne_origin_eq_L' : BB ∪ Kreis_in_Kugel_ohne_Origin = L' := by
  simp [BB, Kreis_in_Kugel_ohne_Origin, L', origin]--, Kreis_in_Kugel, origin, L', L]
  simp [Kreis_in_Kugel, L]
  intro x h1 h2 h3
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

lemma intersection_BB_Kreis_in_Kugel_ohne_Origin_eq_nil : BB ∩ Kreis_in_Kugel_ohne_Origin = ∅ := by
  simp [BB, Kreis_in_Kugel_ohne_Origin]

lemma union_A_B_eq_Kreis : list_union [Kreis_in_Kugel_A, Kreis_in_Kugel_B] = Kreis_in_Kugel_ohne_Origin := by
  simp [list_union, union, Kreis_in_Kugel_B, Kreis_in_Kugel_A, Kreis_in_Kugel_ohne_Origin, Kreis_in_Kugel, origin]
  save ;intro x h1
  simp at h1
  rcases h1 with ⟨n, ⟨h1, h2⟩⟩
  rw [h2]
  simp; save
  apply And.intro
  . apply And.intro
    . ring_nf
      simp only [Real.cos_sq_add_sin_sq]
    . sorry
  . refine Function.ne_iff.mpr ?_ -- TODO sehr gutes ding
    use 0
    simp only [Matrix.cons_val_zero, ne_eq]
    apply_fun (. - 2⁻¹)
    ring_nf
    apply_fun (. * 2)
    ring_nf
    simp only [ne_eq]
    rw  [Real.cos_eq_neg_one_iff]
    intro h3
    sorry


lemma intersection_A_B_eq_nil : Kreis_in_Kugel_A ∩ Kreis_in_Kugel_B = ∅ := by
  simp [Kreis_in_Kugel_A, Kreis_in_Kugel_B]


set_option maxHeartbeats 0
lemma equi_kreis_in_kugel : equidecomposable Kreis_in_Kugel_ohne_Origin Kreis_in_Kugel := by
  rw [equidecomposable]
  use [Kreis_in_Kugel_A, Kreis_in_Kugel_B]
  simp only [List.length_cons, List.length_singleton, Set.coe_setOf, Nat.reduceSucc,
    Set.mem_setOf_eq, exists_and_left, Subtype.exists]; save
  apply And.intro
  . simp [list_intersection, intersection, pairs, list_union, union, intersection_A_B_eq_nil]; save
  apply And.intro
  . exact union_A_B_eq_Kreis
  use [gl_sq_2, gl_one]
  simp only [List.length_nil, Nat.reduceSucc, List.length_cons, List.length_singleton,
    exists_true_left]; save
  use [![-1/2, 0, 0], ![0, 0, 0]]
  simp; save
  use [![1/2, 0, 0], ![0,0,0]]
  

  

      
--- Falsch rum, rotation müsste anders rein als bei Equi
theorem equi_kugel : equidecomposable L' L := by
  apply equidecomposable_subset L' L BB Kreis_in_Kugel_ohne_Origin BB Kreis_in_Kugel
  --
  exact BB_and_Kreis_in_Kugel_ohne_origin_eq_L'
  --
  exact intersection_BB_Kreis_in_Kugel_ohne_Origin_eq_nil
  --
  exact BB_union_Kreis_in_Kugel_eq_L
  --
  rfl
  --
  exact equi_kreis_in_kugel
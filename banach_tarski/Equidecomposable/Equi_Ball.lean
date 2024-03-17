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

noncomputable def rot_sq_2_inv : Matrix (Fin 3) (Fin 3) Real := !![Real.cos (sq_2), -Real.sin sq_2, 0; Real.sin (sq_2), Real.cos (sq_2), 0; 0,0,1]
lemma rot_sq_2_inv_det_ne_zero : Matrix.det rot_sq_2_inv ≠ 0 := by
  simp [rot_sq_2_inv, Matrix.det_fin_three, sq_2]
  rw [@mul_self_add_mul_self_eq_zero]
  intro h1
  cases h1 with
  | intro left right =>
    rw [← Bool.coe_false]
    apply sin_sqrt_2_neq_0
    exact right


noncomputable def gl_sq_2_inv : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero rot_sq_2_inv rot_sq_2_inv_det_ne_zero
lemma coe_gl_sq_2_inv_eq_rot_sq_2_inv : ↑gl_sq_2_inv = rot_sq_2_inv := by
  rfl

------
noncomputable def rot_besser : Matrix (Fin 3) (Fin 3) Real := !![Real.cos (sq_2), Real.sin sq_2, 0; -Real.sin (sq_2), Real.cos (sq_2), 0; 0,0,1]
lemma det_rot_besser : Matrix.det rot_besser ≠ 0 := by
  simp [rot_besser, Matrix.det_fin_three, sq_2]
  rw [@mul_self_add_mul_self_eq_zero]
  intro h1
  cases h1 with
  | intro left right =>
    rw [← Bool.coe_false]
    apply sin_sqrt_2_neq_0
    exact right


noncomputable def gl_rot_besser : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero rot_besser det_rot_besser
lemma coe_rot_besser : ↑gl_rot_besser = rot_besser := by
  rfl




def Kreis_in_Kugel_A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![1/2 * Real.cos (n * sq_2) + 1/2,1/2 * Real.sin (n * sq_2),0]} -- TODO
def Kreis_in_Kugel_B := Kreis_in_Kugel_ohne_Origin \ Kreis_in_Kugel_A

lemma rotate_works : rotate gl_rot_besser ![1/2 * Real.cos sq_2,1/2 * Real.sin sq_2, 0] = ![-1/2,0,0] := by
  simp [rotate, coe_rot_besser, rot_besser]
  ext i
  fin_cases i
  simp
  ring
  sorry -- stimmt
  simp
  ring
  simp

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


lemma equi_kreis_in_kugel_aux : {w | ∃ a ∈ Kreis_in_Kugel_A, translate ![2⁻¹, 0, 0]
    (rotate gl_sq_2_inv (translate ![-1 / 2, 0, 0] a)) = w} ∪
    {w | ∃ v ∈ Kreis_in_Kugel_B, rotate 1 v = w} =
  Kreis_in_Kugel := by
  ext x
  apply Iff.intro
  . intro h
    simp [Kreis_in_Kugel_A, translate, rotate, coe_gl_sq_2_inv_eq_rot_sq_2_inv, Matrix.vecHead, Matrix.vecTail, rot_sq_2_inv, Kreis_in_Kugel_B, Kreis_in_Kugel_ohne_Origin, origin, Kreis_in_Kugel] at h; save
    rcases h with ⟨x1, ⟨⟨n,⟨h3, h1⟩⟩, h2⟩⟩ | ⟨⟨⟨h2, ⟨h3, h4⟩⟩, h1⟩, h⟩; save
    . simp [← h2]
      simp [Kreis_in_Kugel]
      apply And.intro
      . simp [h1, Real.cos_sq]; save
        ring; save
        simp [Real.cos_sq]; save
        sorry
      . simp [h1]; save
        sorry
    . simp [Kreis_in_Kugel, h3, h4, h2]; save

  . intro h
    simp only [Set.mem_union, Set.mem_setOf_eq]; save
    by_cases hc:(∃ v ∈ Kreis_in_Kugel_B, rotate 1 v = x)
    . right; exact hc
    . left
      simp [rotate] at hc; save
      by_cases hc2:(x ≠ origin)
      use translate ![1/2, 0, 0] (rotate gl_rot_besser (translate ![-1/2, 0, 0] x))
      simp [translate, rotate, coe_rot_besser, rot_besser, Matrix.vecHead, Matrix.vecTail]; save
      apply And.intro
      . simp [Kreis_in_Kugel_B] at hc; save
        apply hc
        simp [Kreis_in_Kugel_ohne_Origin, h, hc2]; save

      . have h2 : x ∈ Kreis_in_Kugel_A := by
          simp [Kreis_in_Kugel_B] at hc; save
          apply hc
          simp [Kreis_in_Kugel_ohne_Origin, h, hc2]; save
        simp [Kreis_in_Kugel_A] at h2
        rcases h2 with ⟨a, ⟨h1, h2⟩⟩; save
        rw [h2]
        simp [translate, rotate, coe_gl_sq_2_inv_eq_rot_sq_2_inv, rot_sq_2_inv]; save
        ext i
        fin_cases i
        --
        simp; save
        apply_fun (. * 2 - 1)
        ring_nf
        simp [Real.cos_sq, Real.sin_sq_eq_half_sub]; save
        ring; save
        --
        rw [Function.Injective]
        intro a1 a2
        intro ha
        aesop_subst h2
        simp_all only [sub_left_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false, ne_eq]
        ----
        simp
        ring
        simp [Real.cos_sq, Real.sin_sq_eq_half_sub]
        ring
        --
        simp

      . simp at hc2; save
        simp [hc2, Kreis_in_Kugel_A]; save
        use ![1/2 * Real.cos sq_2 + 1/2, 1/2 * Real.sin sq_2, 0]
        apply And.intro
        . use 1
          simp; save
        . simp [translate, Matrix.vecHead, Matrix.vecTail]
          ring
          simp




          simp [rot_sq_2_inv, translate, rotate, coe_gl_sq_2_inv_eq_rot_sq_2_inv, origin, Matrix.vecHead, Matrix.vecTail]; save
          ext i
          fin_cases i
          . simp; save
            ring; save
            sorry
          . sorry
          . sorry






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
  use [gl_sq_2_inv, gl_one]
  simp only [List.length_nil, Nat.reduceSucc, List.length_cons, List.length_singleton,
    exists_true_left]; save
  use [![-1/2, 0, 0], ![0, 0, 0]]
  simp; save
  use [![1/2, 0, 0], ![0,0,0]]
  simp [translate_list, translate_zero, remove_first, rotate_set, rotate_list, translate_set, coe_gl_one_eq_one, list_union, union]; save
  exact equi_kreis_in_kugel_aux

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

import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Equi_Kreis

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

---- TODO kreis nicht mit weirder formel sondern mit funktion die den normalen kreis verschiebt und skaliert
--- -> beweis dass ein verschobenener Kreis immnernoch equidekomponierbar ist
def Kreis_in_Kugel : Set r_3 := {p : r_3 | ((2 * (p 0) - 1)) ^ 2 + (2 * (p 1)) ^ 2 = 1 ∧ p 2 = 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1}
def Kreis_in_Kugel_ohne_Origin : Set r_3 := Kreis_in_Kugel \ {origin}

def BB := L \ Kreis_in_Kugel

def Kreis_in_Kugel_A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![1/2 * Real.cos (n * sq_2) + 1/2,1/2 * Real.sin (n * sq_2),0]} -- TODO
def Kreis_in_Kugel_B := Kreis_in_Kugel \ Kreis_in_Kugel_A

--def rot_sq_2_around_point : Matrix (Fin 3) (Fin 3) Real := !![]

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


lemma union_A_B_eq_Kreis : list_union [Kreis_in_Kugel_A, Kreis_in_Kugel_B] = Kreis_in_Kugel := by
  simp [list_union, union, Kreis_in_Kugel_A, Kreis_in_Kugel_B, Kreis_in_Kugel]
  intro a n _ h2
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

lemma equi_kreis_in_kugel_aux_1 (x : r_3) :  x ∈
    {w | ∃ a ∈ Kreis_in_Kugel_A, translate ![2⁻¹, 0, 0] (rotate gl_sq_2 (translate ![-1 / 2, 0, 0] a)) = w} ∪
      {w | ∃ a ∈ Kreis_in_Kugel_B, translate ![0, 0, 0] (rotate 1 (translate ![0, 0, 0] a)) = w} →
  x ∈ Kreis_in_Kugel_ohne_Origin := by sorry

lemma equi_kreis_in_kugel_aux_2 (x: r_3) : x ∈ Kreis_in_Kugel_ohne_Origin →
  x ∈
    {w | ∃ a ∈ Kreis_in_Kugel_A, translate ![2⁻¹, 0, 0] (rotate gl_sq_2 (translate ![-1 / 2, 0, 0] a)) = w} ∪
      {w | ∃ a ∈ Kreis_in_Kugel_B, translate ![0, 0, 0] (rotate 1 (translate ![0, 0, 0] a)) = w} := by sorry

set_option maxHeartbeats 0
lemma equi_kreis_in_kugel : equidecomposable Kreis_in_Kugel Kreis_in_Kugel_ohne_Origin := by
  rw [equidecomposable]
  use [Kreis_in_Kugel_A, Kreis_in_Kugel_B]
  simp; save
  apply And.intro
  . simp [list_intersection, list_union, union, pairs, intersection, Kreis_in_Kugel_A, Kreis_in_Kugel_B]; save
  . apply And.intro
    . exact union_A_B_eq_Kreis
    . use [gl_sq_2, gl_one]
      simp
      use [![-1/2,0,0], ![0,0,0]]
      simp;save
      use [![1/2,0,0], ![0,0,0]]
      simp  [translate_list, rotate_list, translate_set, rotate_set, coe_gl_one_eq_one, remove_first, list_union, union]
      ext x
      apply Iff.intro
      . apply equi_kreis_in_kugel_aux_1
      . apply equi_kreis_in_kugel_aux_2

      /-
      save; simp [list_union, translate_list, rotate_list, Matrix.vecHead, Matrix.vecTail,coe_gl_one_eq_one,Kreis_in_Kugel,
        union, translate_set, rotate_set, translate, rotate, remove_first, Kreis_in_Kugel_A, Kreis_in_Kugel_B, Kreis_in_Kugel_ohne_Origin]
      ;save
      ext x
      apply Iff.intro;save
      . intro h
        cases h with
        | inl h =>
          simp at *
          cases h with
          | intro w h =>
          cases h with
          | intro left right =>
          rw [← right]
          cases left with
          | intro w1 h1 =>
          cases h1 with
          | intro left1 right1 =>
          rw [right1]
          simp [origin,coe_gl_sq_2_eq_rot_sq_2, rot_sq_2]
          save
          apply And.intro
          apply And.intro
          ring
          simp [Real.cos_sq, Real.sin_sq_eq_half_sub]; save
          ring; save
          --
          apply And.intro
          . ring; save
            field_simp
            rw [@add_assoc]
            rw [← Real.cos_sub]
            ring_nf
            rw [← @le_neg_add_iff_add_le]
            ring_nf
            norm_num
            apply Real.cos_le_one
          . ring_nf
            field_simp
            rw [@le_iff_exists_nonneg_add]
            use -Real.sin (↑w1 * sq_2) * Real.cos sq_2 / 2 + (2 + Real.cos (↑w1 * sq_2) * Real.sin sq_2) / 2
            ring_nf
            simp; save
            field_simp
            sorry
          . refine Function.ne_iff.mpr ?_
            use 0
            simp
            ring_nf
            apply_fun (. * 2 - 1)
            ring
            rw [← Real.cos_sub]
            simp only [ne_eq, Real.cos_eq_neg_one_iff, not_exists]; save
            intro x hx
            ring_nf! at hx; save
            have hx2 : Real.pi * (↑x * 2 + 1) = (↑w1 - 1) * sq_2 := by
              ring_nf
              rw [← hx]
            
            have hx3 : ∃ q w: ℚ, Real.pi * w = sq_2 * q := by
              use (↑w1 - 1)
              use ↑(x * 2 + 1)
              simp [hx2]
              ring
            
            have hx4 : ∃ q : ℚ, Real.pi = q * sq_2 := by
              cases hx3 with
              | intro w h =>
              cases h with
              | intro q h =>
              use (w/q)
              simp
              save
              sorry
            
            cases hx4 with 
            | intro q h =>
            rw [← Bool.coe_false]
            apply pi_sqrt_two
            use q
          

        | inr h => 
          simp [origin]; save
          rcases h with ⟨w, ⟨⟨h2, ⟨h3, h4⟩⟩, h⟩, h1⟩
          apply And.intro
          apply And.intro
          simp only [← h1, h3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h2]
          --
          apply And.intro
          simp [← h1, h3]
          --
          simp [← h1, h4]
          --
          rw [← h1]
          apply_fun (. - (2 * w 1)^2) at h2
          simp at h2
          sorry
      save
      intro h1
      simp;save
      rcases h1 with ⟨⟨h2,⟨h3, ⟨h4, h5⟩⟩⟩, h1⟩
      sorry-/
      

theorem equi_kugel : equidecomposable L L' := by
  apply equidecomposable_subset L L' BB Kreis_in_Kugel BB Kreis_in_Kugel_ohne_Origin
  --
  exact Kreis_subset_L
  --
  exact BB_Kreis_in_Kugel_no_intersection
  --
  exact BB_and_Kreis_in_Kugel_ohne_origin_eq_L'
  --
  rfl
  --
  exact equi_kreis_in_kugel

import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Equi_Kreis
import banach_tarski.Equidecomposable.Rotations

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex


def Kreis_in_Kugel : Set r_3 := {p : r_3 | ((2 * (p 0) + 1)) ^ 2 + (2 * (p 1)) ^ 2 = 1 ∧ p 2 = 0 ∧ -p 0 ≤ 1}
def Kreis_in_Kugel_ohne_Origin : Set r_3 := Kreis_in_Kugel \ {origin}

def Part_B := L' \ Kreis_in_Kugel_ohne_Origin


def Kreis_in_Kugel_A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![1/2 * Real.cos (n * sq_2) - 1/2,1/2 * Real.sin (n * sq_2),0]} -- TODO
def Kreis_in_Kugel_B := Kreis_in_Kugel_ohne_Origin \ Kreis_in_Kugel_A


lemma Kreis_subset_L : Kreis_in_Kugel ⊆ L := by
  simp [Kreis_in_Kugel,L]
  intro a h1 h2 h3
  rw [h2]
  simp
  apply_fun (. - (2 * a 0 + 1) ^2) at h1
  ring_nf at h1
  apply_fun (. / 4) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3

lemma Part_B_union_Kreis_in_Kugel_eq_L : Part_B ∪ Kreis_in_Kugel = L := by
  simp [Part_B, L', Kreis_in_Kugel_ohne_Origin]
  rw [Set.diff_diff]
  rw [Set.union_diff_cancel]
  simp only [Set.diff_union_self, Set.union_eq_left]

  exact Kreis_subset_L

  simp [origin, Kreis_in_Kugel]



lemma Part_B_and_Kreis_in_Kugel_ohne_origin_eq_L' : Part_B ∪ Kreis_in_Kugel_ohne_Origin = L' := by
  simp [Part_B, Kreis_in_Kugel_ohne_Origin, L', origin]
  simp [Kreis_in_Kugel, L]
  intro x h1 h2 h3
  simp [h2]
  apply_fun (. - (2 * x 0 + 1) ^2) at h1
  ring_nf at h1
  apply_fun (. / 4) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3

lemma intersection_Part_B_Kreis_in_Kugel_ohne_Origin_eq_nil : Part_B ∩ Kreis_in_Kugel_ohne_Origin = ∅ := by
  simp [Part_B, Kreis_in_Kugel_ohne_Origin]

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
    . rw [← @tsub_le_iff_left]
      norm_num
      have h_c : -(1 / 2) ≤ 1 / 2 * Real.cos (↑n * sq_2) := calc
        -(1 / 2) ≤ (1 / 2) * (-1) := by simp
        _ ≤ (1 / 2) * (Real.cos (n * sq_2)) := by
          gcongr
          exact Real.neg_one_le_cos (n * sq_2)
      exact h_c

  . refine Function.ne_iff.mpr ?_
    use 0
    simp only [Matrix.cons_val_zero, ne_eq]
    apply_fun (. - 2⁻¹)
    ring_nf
    apply_fun (. * 2)
    ring_nf
    simp only [ne_eq]
    rw [← ne_eq]
    apply_fun (. + 2)
    ring_nf
    rw [ne_eq]
    rw  [Real.cos_eq_one_iff]

    intro h3
    have h: ∃ q : ℚ, Real.pi = q * sq_2 := by
      rcases h3 with ⟨n1, h3⟩
      have hn1 : (↑n1 : Real) ≠ 0 := by
        apply_fun (. / (2 * Real.pi)) at h3
        ring_nf at h3
        rw [mul_assoc] at h3
        rw [mul_inv_cancel] at h3
        simp at h3
        rw [h3]
        simp
        intro hx
        rcases hx with ⟨a | c⟩ | b
        convert a
        simp [Real.pi_ne_zero]
        --
        convert c
        simp
        exact Nat.pos_iff_ne_zero.mp h1
        --
        convert b
        simp [sq_2]
        --
        simp [Real.pi_ne_zero]

      use (↑n / (↑n1 * 2))
      field_simp
      rw [← h3]
      ring

    rw [← Bool.coe_false]
    apply pi_sqrt_two
    exact h


lemma intersection_A_B_eq_nil : Kreis_in_Kugel_A ∩ Kreis_in_Kugel_B = ∅ := by
  simp [Kreis_in_Kugel_A, Kreis_in_Kugel_B]


lemma le_lemma (n : Nat):
      Real.sin (↑n * sq_2) * Real.sin sq_2 * (-1 / 2) ≤
       1 / 2 + Real.cos (↑n * sq_2) * Real.cos sq_2 * (1 / 2) := by
        rw [← @tsub_le_iff_right]
        ring_nf
        rw [← mul_rotate]
        rw [mul_assoc]
        rw [← mul_rotate]
        rw [mul_assoc]
        rw [← mul_add]
        rw [add_comm]
        rw [← Real.cos_sub]
        have h_c : -1/2 * Real.cos (↑n * sq_2 - sq_2) ≤ 1 / 2 := calc
          (-1/2) * Real.cos (↑n * sq_2 - sq_2) ≤ (-1/2) * (-1) := by
             rw [mul_le_mul_left_of_neg]
             apply Real.neg_one_le_cos (↑n * sq_2 - sq_2)
             norm_num
          _  ≤ 1 / 2 := by
            norm_num
        exact h_c


lemma equi_kreis_in_kugel_aux : {w | ∃ a ∈ Kreis_in_Kugel_A, translate ![-1/2, 0, 0]
    (rotate gl_sq_2 (translate ![2⁻¹, 0, 0] a)) = w} ∪
    {w | ∃ v ∈ Kreis_in_Kugel_B, rotate 1 v = w} =
  Kreis_in_Kugel := by
  ext x
  apply Iff.intro
  . intro h
    simp [Kreis_in_Kugel_A, translate, rotate, coe_gl_sq_2_eq_rot_sq_2, Matrix.vecHead, Matrix.vecTail, rot_sq_2, Kreis_in_Kugel_B, Kreis_in_Kugel_ohne_Origin, origin, Kreis_in_Kugel] at h; save
    rcases h with ⟨x1, ⟨⟨n,⟨_, h1⟩⟩, h2⟩⟩ | ⟨⟨⟨h2, ⟨h3, h4⟩⟩, _⟩, _⟩; save
    . simp [← h2]
      simp [Kreis_in_Kugel]
      apply And.intro
      . simp [h1, Real.cos_sq]; save
        ring_nf; save
        simp [Real.cos_sq, Real.sin_sq_eq_half_sub]; save
        ring_nf
      . simp [h1]; save
        ring_nf; save
        apply le_lemma

    . simp [Kreis_in_Kugel, h3, h4, h2]; save

  . intro h
    simp only [Set.mem_union, Set.mem_setOf_eq]; save
    by_cases hc:(∃ v ∈ Kreis_in_Kugel_B, rotate 1 v = x)
    . right; exact hc
    . left
      simp [rotate] at hc; save
      by_cases hc2:(x ≠ origin)
      use translate ![-1/2, 0, 0] (rotate gl_sq_2_inv (translate ![1/2, 0, 0] x))
      simp [translate, rotate, coe_gl_sq_2_inv_eq_rot_sq_2_inv, rot_sq_2_inv, Matrix.vecHead, Matrix.vecTail]; save
      --
      have h2 : x ∈ Kreis_in_Kugel_A := by
          simp [Kreis_in_Kugel_B] at hc; save
          apply hc
          simp [Kreis_in_Kugel_ohne_Origin, h, hc2]; save
      --
      simp [Kreis_in_Kugel_A] at h2
      rcases h2 with ⟨a, ⟨_, h2⟩⟩; save
      apply And.intro
      .   simp [Kreis_in_Kugel_B] at hc; save
          simp [Kreis_in_Kugel_A]
          use a + 1
          simp [h2, hc2]
          ext i
          fin_cases i
          . simp
            ring_nf
            field_simp
            apply_fun (. + 1)
            ring_nf
            rw [← Real.cos_add]
            --
            rw [Function.Injective]
            intro a₁ a₂ a_1
            aesop_subst h2
            simp_all only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false, ne_eq]
            simp at a_1
            simp [a_1]
            --
          . simp
            ring_nf
            field_simp
            rw [Real.sin_add]
            rw [add_comm]

          . simp

      . rw [h2]
        simp [translate, rotate, coe_gl_sq_2_eq_rot_sq_2, rot_sq_2]; save
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
        --
        simp
        ring_nf
        simp [Real.cos_sq, Real.sin_sq_eq_half_sub]
        ring
        --
        simp

      . simp at hc2; save
        simp [hc2, Kreis_in_Kugel_A]; save
        use ![1/2 * Real.cos sq_2 - 1/2, 1/2 * Real.sin sq_2, 0]
        apply And.intro
        . use 1
          simp; save

        . simp [rot_sq_2, translate, rotate, coe_gl_sq_2_eq_rot_sq_2, origin, Matrix.vecHead, Matrix.vecTail]; save
          ext i
          fin_cases i
          . simp; save
            ring_nf; save
            apply_fun (. * 2 + 1)
            ring_nf
            simp
            --
            simp [Function.Injective]
            ---
          . simp
            ring
          . simp



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
  use [![1/2, 0, 0], ![0, 0, 0]]
  simp; save
  use [![-1/2, 0, 0], ![0,0,0]]
  simp [translate_list, translate_zero, remove_first, rotate_set, rotate_list, translate_set, coe_gl_one_eq_one, list_union, union]; save
  exact equi_kreis_in_kugel_aux



theorem equi_kugel : equidecomposable L' L := by
  apply equidecomposable_subset L' L Part_B Kreis_in_Kugel_ohne_Origin Part_B Kreis_in_Kugel
  --
  exact Part_B_and_Kreis_in_Kugel_ohne_origin_eq_L'
  --
  exact intersection_Part_B_Kreis_in_Kugel_ohne_Origin_eq_nil
  --
  exact Part_B_union_Kreis_in_Kugel_eq_L
  --
  rfl
  --
  exact equi_kreis_in_kugel

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
  simp only [Kreis_in_Kugel, Fin.isValue, L, Set.setOf_subset_setOf, and_imp]
  intro a h1 h2 h3
  rw [h2]
  simp only [Fin.isValue, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_le_one]
  apply_fun (. - (2 * a 0 + 1) ^2) at h1
  ring_nf at h1
  apply_fun (. / 4) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3

lemma Part_B_union_Kreis_in_Kugel_eq_L : Part_B ∪ Kreis_in_Kugel = L := by
  simp only [Part_B, L', Kreis_in_Kugel_ohne_Origin]
  rw [Set.diff_diff]
  rw [Set.union_diff_cancel]
  simp only [Set.diff_union_self, Set.union_eq_left]

  exact Kreis_subset_L

  simp only [origin, Kreis_in_Kugel, Fin.isValue, Set.singleton_subset_iff, Set.mem_setOf_eq,
    Matrix.cons_val_zero, mul_zero, zero_add, one_pow, Matrix.cons_val_one, Matrix.head_cons, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Matrix.cons_val_two,
    Matrix.tail_cons, neg_zero, zero_le_one, and_self]



lemma Part_B_and_Kreis_in_Kugel_ohne_origin_eq_L' : Part_B ∪ Kreis_in_Kugel_ohne_Origin = L' := by
  simp only [Part_B, L', L, Fin.isValue, origin, Kreis_in_Kugel_ohne_Origin, Kreis_in_Kugel,
    Set.diff_union_self, Set.union_eq_left, Set.diff_singleton_subset_iff,
    Set.insert_diff_singleton, Set.mem_setOf_eq, Matrix.cons_val_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Matrix.cons_val_one, Matrix.head_cons, add_zero, Real.sqrt_zero,
    Matrix.cons_val_two, Matrix.tail_cons, zero_le_one, Set.insert_eq_of_mem,
    Set.setOf_subset_setOf, and_imp]
  intro x h1 h2 h3
  simp only [Fin.isValue, h2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_le_one]
  apply_fun (. - (2 * x 0 + 1) ^2) at h1
  ring_nf at h1
  apply_fun (. / 4) at h1
  ring_nf at h1
  rw [h1]
  ring_nf
  exact h3

lemma intersection_Part_B_Kreis_in_Kugel_ohne_Origin_eq_nil : Part_B ∩ Kreis_in_Kugel_ohne_Origin = ∅ := by
  simp only [Part_B, Kreis_in_Kugel_ohne_Origin, Set.diff_inter_self]

lemma union_A_B_eq_Kreis : list_union [Kreis_in_Kugel_A, Kreis_in_Kugel_B] = Kreis_in_Kugel_ohne_Origin := by
  simp only [list_union, Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq, Subtype.exists,
    gt_iff_lt, exists_prop, Kreis_in_Kugel_B, Kreis_in_Kugel_ohne_Origin, Kreis_in_Kugel,
    Fin.isValue, origin, List.foldl_cons, union, Set.empty_union, Set.union_diff_self,
    List.foldl_nil, Set.union_eq_right]
  intro x h1
  simp only [Set.mem_setOf_eq] at h1
  rcases h1 with ⟨n, ⟨h1, h2⟩⟩
  rw [h2]
  simp only [Fin.isValue, Set.mem_diff, Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀,
    Matrix.cons_val_two, Matrix.tail_cons, neg_sub, tsub_le_iff_right, true_and,
    Set.mem_singleton_iff]
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
        simp only [mul_one, one_div] at h3
        rw [h3]
        simp only [ne_eq, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, OfNat.ofNat_ne_zero, or_false]
        intro hx
        rcases hx with ⟨a | c⟩ | b
        convert a
        simp only [Real.pi_ne_zero]
        --
        convert c
        simp only [false_iff]
        exact Nat.pos_iff_ne_zero.mp h1
        --
        convert b
        simp only [sq_2, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero]
        --
        simp only [ne_eq, Real.pi_ne_zero, not_false_eq_true]

      use (↑n / (↑n1 * 2))
      field_simp
      rw [← h3]
      ring

    rw [← Bool.coe_false]
    apply pi_sqrt_two
    exact h


lemma intersection_A_B_eq_nil : Kreis_in_Kugel_A ∩ Kreis_in_Kugel_B = ∅ := by
  simp only [Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt,
    exists_prop, Kreis_in_Kugel_B, Set.inter_diff_self]


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
    simp only [Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq, Subtype.exists,
      gt_iff_lt, exists_prop, translate, rotate, Matrix.cons_add, Matrix.vecHead, Fin.isValue,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, zero_add, Fin.succ_one_eq_two,
      Matrix.empty_add_empty, coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, Matrix.vecMul_cons,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, mul_one,
      Matrix.empty_vecMul, add_zero, Matrix.add_cons, Kreis_in_Kugel_B, Kreis_in_Kugel_ohne_Origin,
      Kreis_in_Kugel, origin, Set.mem_diff, Set.mem_singleton_iff, not_exists, not_and,
      Units.val_one, Matrix.vecMul_one, exists_eq_right, Set.mem_union] at h
    rcases h with ⟨x1, ⟨⟨n,⟨_, h1⟩⟩, h2⟩⟩ | ⟨⟨⟨h2, ⟨h3, h4⟩⟩, _⟩, _⟩
    . simp only [← h2, Fin.isValue]
      simp only [Fin.isValue, Kreis_in_Kugel, Set.mem_setOf_eq, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, neg_add_rev,
        add_neg_le_iff_le_add]
      apply And.intro
      . simp only [h1, Fin.isValue, Matrix.cons_val_zero, add_sub_cancel, Matrix.cons_val_one,
        Matrix.head_cons]
        ring_nf
        simp only [Real.cos_sq, one_div, Real.sin_sq_eq_half_sub]
        ring_nf
      . simp only [h1, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel, true_and]
        ring_nf
        apply le_lemma

    . simp only [Kreis_in_Kugel, Fin.isValue, Set.mem_setOf_eq, h2, h3, h4, and_self]

  . intro h
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hc:(∃ v ∈ Kreis_in_Kugel_B, rotate 1 v = x)
    . right
      exact hc
    . left
      simp only [rotate, Units.val_one, Matrix.vecMul_one, exists_eq_right] at hc
      by_cases hc2:(x ≠ origin)
      use translate ![-1/2, 0, 0] (rotate gl_sq_2_inv (translate ![1/2, 0, 0] x))
      simp only [translate, rotate, one_div, Matrix.cons_add, Matrix.vecHead, Fin.isValue,
        Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, zero_add, Fin.succ_one_eq_two,
        Matrix.empty_add_empty, coe_gl_sq_2_inv_eq_rot_sq_2_inv, rot_sq_2_inv, Matrix.vecMul_cons,
        Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
        Matrix.cons_val_one, mul_neg, Matrix.cons_val_two, Matrix.cons_val_fin_one, mul_one,
        Matrix.empty_vecMul, add_zero, Matrix.add_cons]
      --
      have h2 : x ∈ Kreis_in_Kugel_A := by
          simp only [Kreis_in_Kugel_B, Set.mem_diff, not_and, not_not] at hc
          apply hc
          simp only [Kreis_in_Kugel_ohne_Origin, Set.mem_diff, h, Set.mem_singleton_iff, hc2,
            not_false_eq_true, and_self]
      --
      simp only [Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq, Subtype.exists,
        gt_iff_lt, exists_prop] at h2
      rcases h2 with ⟨a, ⟨_, h2⟩⟩
      apply And.intro
      . simp only [Kreis_in_Kugel_B, Set.mem_diff, not_and, not_not] at hc
        simp only [Fin.isValue, Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq,
          Subtype.exists, gt_iff_lt, exists_prop]
        use a + 1
        simp only [add_pos_iff, zero_lt_one, or_true, h2, Fin.isValue, Matrix.cons_val_zero,
          add_sub_cancel, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Nat.cast_add, Nat.cast_one, true_and]
        ext i
        fin_cases i
        . simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
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
          simp only [add_left_inj] at a_1
          apply a_1
          --
        . simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
          ring_nf
          field_simp
          rw [Real.sin_add]
          rw [add_comm]

        . simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

      . rw [h2]
        simp only [Fin.isValue, Matrix.cons_val_zero, add_sub_cancel, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, coe_gl_sq_2_eq_rot_sq_2,
          rot_sq_2, Matrix.vecMul_cons, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_zero,
          Matrix.smul_empty, zero_smul, Matrix.empty_vecMul, add_zero, Pi.add_apply]
        ext i
        fin_cases i
        --
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        apply_fun (. * 2 - 1)
        ring_nf
        simp only [Real.cos_sq, one_div, Real.sin_sq_eq_half_sub]
        ring
        --
        rw [Function.Injective]
        intro a1 a2
        intro ha
        aesop_subst h2
        simp_all only [sub_left_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false, ne_eq]
        --
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
        ring_nf
        simp only [Real.cos_sq, one_div, Real.sin_sq_eq_half_sub]
        ring
        --
        simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

      . simp only [ne_eq, not_not] at hc2
        simp only [Kreis_in_Kugel_A, Set.coe_setOf, one_div, Set.mem_setOf_eq, Subtype.exists,
          gt_iff_lt, exists_prop, hc2]
        use ![1/2 * Real.cos sq_2 - 1/2, 1/2 * Real.sin sq_2, 0]
        apply And.intro
        . use 1
          simp only [zero_lt_one, one_div, Nat.cast_one, one_mul, and_self]

        . simp only [translate, rotate, one_div, Matrix.add_cons, Matrix.vecHead, Fin.isValue,
            Matrix.cons_val_zero, add_sub_cancel, Matrix.vecTail, Function.comp_apply,
            Fin.succ_zero_eq_one, Matrix.cons_val_one, zero_add, Fin.succ_one_eq_two,
            Matrix.cons_val_two, Matrix.cons_val_fin_one, add_zero, Matrix.empty_add_empty,
            coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, Matrix.vecMul_cons, Matrix.smul_cons, smul_eq_mul,
            mul_neg, mul_zero, Matrix.smul_empty, zero_smul, Matrix.empty_vecMul, origin]
          ext i
          fin_cases i
          . simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
            ring_nf
            apply_fun (. * 2 + 1)
            ring_nf
            simp only [Real.cos_sq_add_sin_sq]
            --
            simp only [Function.Injective, add_left_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero,
              or_false, imp_self, forall_const]
            ---
          . simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
            ring
          . simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]


lemma equi_kreis_in_kugel : equidecomposable Kreis_in_Kugel_ohne_Origin Kreis_in_Kugel := by
  rw [equidecomposable]
  use [Kreis_in_Kugel_A, Kreis_in_Kugel_B]
  simp only [List.length_cons, Set.coe_setOf, Set.mem_setOf_eq, exists_and_left, Subtype.exists]
  apply And.intro
  . simp only [list_intersection, list_union, pairs, List.map_cons, List.map_nil, List.append_nil,
    List.singleton_append, intersection, intersection_A_B_eq_nil, List.foldl_cons, union,
    Set.union_self, List.foldl_nil]
  apply And.intro
  . exact union_A_B_eq_Kreis
  use [gl_sq_2, gl_one]
  simp only [List.length_nil, Nat.reduceSucc, List.length_cons, List.length_singleton,
    exists_true_left]
  use [![1/2, 0, 0], ![0, 0, 0]]
  simp
  use [![-1/2, 0, 0], ![0,0,0]]
  simp [translate_list, translate_zero, remove_first, rotate_set, rotate_list, translate_set, coe_gl_one_eq_one, list_union, union]
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

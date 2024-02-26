import banach_tarski.Definitions
import Mathlib.Data.Real.Sqrt

theorem adjugate_fin_three (a b c d e f g h i: Real) :
  Matrix.adjugate (Matrix.of ![![a, b, c], ![d, e, f], ![g, h, i]])=
  Matrix.of ![![e * i - f * h, -(b * i) + c * h, b * f - c * e],
            ![-(d * i) + f * g, a * i - c * g, -(a * f) + c * d],
            ![d * h - e * g, -(a * h) + b * g, a * e - b * d]] := by

  ext h1 h2
  fin_cases h1
  simp
  rw [Matrix.adjugate_apply]
  rw [Matrix.det_fin_three]
  repeat rw [Matrix.updateRow_apply]
  simp
  fin_cases h2
  repeat
    repeat simp
    repeat rw [if_neg]
    rw [Pi.single_apply]
    repeat rw [if_neg]
    simp

    repeat
      rw [← ne_eq]
      rw [@ne_iff_lt_or_gt]
      right
      exact Fin.coe_sub_iff_lt.mp rfl
  ---
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  simp
  rw [Pi.single_apply]
  rw [if_neg]
  simp

  rw [← ne_eq]
  rw [@ne_iff_lt_or_gt]
  right
  exact Fin.coe_sub_iff_lt.mp rfl

  repeat
    rw [@Fin.eq_mk_iff_val_eq]
    simp

  ---

  rw [Matrix.adjugate_apply]
  rw [Matrix.det_fin_three]
  repeat rw [Matrix.updateRow_apply]
  simp
  fin_cases h2
  simp
  rw [Pi.single_apply]
  rw [if_neg]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_neg]
  rw [Pi.single_apply]
  rw [if_neg]
  simp
  --
  rw [@Fin.eq_mk_iff_val_eq]
  simp

  repeat
    rw [← ne_eq]
    rw [@ne_iff_lt_or_gt]
    right
    exact Fin.coe_sub_iff_lt.mp rfl

  rw [@Fin.eq_mk_iff_val_eq]
  simp

  rw [← ne_eq]
  rw [@ne_iff_lt_or_gt]
  right
  exact Fin.coe_sub_iff_lt.mp rfl
  ---
  simp
  repeat rw [if_neg]
  repeat rw [Pi.single_apply]
  rw [if_pos]
  rw [if_neg]
  simp
  --
  rw [@Fin.eq_mk_iff_val_eq]
  simp

  rw [@Fin.eq_mk_iff_val_eq]
  simp

  repeat
    rw [← ne_eq]
    rw [@ne_iff_lt_or_gt]
    right
    exact Fin.coe_sub_iff_lt.mp rfl

  ---
  simp
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  simp
  repeat rw [Pi.single_apply]
  rw [if_neg]
  rw [if_pos]
  simp
  --
  repeat
    rw [@Fin.eq_mk_iff_val_eq]
    simp

  rw [Matrix.adjugate_apply]
  rw [Matrix.det_fin_three]
  repeat rw [Matrix.updateRow_apply]
  simp
  fin_cases h2
  simp
  rw [if_neg]
  rw [if_neg]
  rw [if_neg]
  rw [if_neg]
  rw [if_neg]
  rw [if_neg]
  repeat rw [Pi.single_apply]
  rw [if_neg]
  rw [if_neg]
  rw [if_pos]
  simp
  --
  repeat
    rw [@Fin.eq_mk_iff_val_eq]
    simp
  ---
  simp

  repeat rw [if_neg]
  repeat rw [Pi.single_apply]
  rw [if_neg]
  rw [if_pos]
  rw [if_neg]
  simp
  --
  repeat
    rw [@Fin.eq_mk_iff_val_eq]
    simp

  ---
  repeat simp
  repeat
    rw [if_pos]
    rw [if_neg]
    rw [if_neg]

  repeat rw [Pi.single_apply]
  rw [if_pos]
  rw [if_neg]
  rw [if_neg]
  --
  simp
  repeat
    rw [@Fin.eq_mk_iff_val_eq]
    simp


-- Matlab
--syms a b c d e f g h i n
--A = [(a*((1/3) ^ n)) (b * sqrt(2) * (1/3) ^ n) (c*((1/3) ^ n));
--    (d * sqrt(2) * (1/3) ^ n) (e *((1/3) ^ n)) (f * sqrt(2) * (1/3) ^ n);
--    (g*((1/3) ^ n)) (h * sqrt(2) * (1/3) ^ n) (i*((1/3) ^ n))];
--D = inv(A)

variable (n m: Nat)

noncomputable def general_word_form  (a b c d e f g h i: ℤ) (n: Nat): Matrix (Fin 3) (Fin 3) Real :=
  !![(a : Real) * (1/3 ^ n),b * Real.sqrt 2 * (1/3 ^ n), (c : Real) * (1/3 ^ n);
    d * Real.sqrt 2 * (1/3 ^ n), (e : Real) * (1/3 ^ n), f * Real.sqrt 2 * (1/3 ^ n);
    (g: Real) * (1/3 ^ n), h * Real.sqrt 2 * (1/3 ^ n), (i : Real) * (1/3 ^ n)]



def general_word_form_prop (x: GL (Fin 3) Real) (n : Nat) :=
  ∃ a b c d e f g h i, x = general_word_form a b c d e f g h i n

theorem general_word_form_h_k : ∀ x ∈ erzeuger, general_word_form_prop x n:= by
  intro x h
  rw [general_word_form_prop]
  cases h with
  | inl ha =>
    use 3
    use 0
    use 0

    use 0
    use 1
    use -2

    use 0
    use 2
    use 1

    rw [general_word_form]
    simp
    rw [ha]
    sorry
    --rw [coe_gl_a_eq_matrix_a]
    --rw [matrix_a]
    --ring_nf

  | inr h_b =>
    sorry




theorem general_word_form_h_1 : general_word_form_prop 1 n := by
  rw [general_word_form_prop]

  sorry

theorem general_word_form_h_mul : ∀ x y : GL (Fin 3) Real, general_word_form_prop x n ->
    general_word_form_prop y n -> general_word_form_prop (x * y) (n + n):= by
    intro x y h1 h2
    rw [general_word_form_prop] at h1
    rcases h1 with ⟨a, b, c, d, e, f, g, h, i, h1'⟩

    rw [general_word_form_prop] at h2
    rcases h2 with ⟨aa, bb, cc, dd, ee, ff, gg, hh, ii, h2'⟩

    rw [general_word_form_prop]

    rw [@Matrix.GeneralLinearGroup.coe_mul] -- bestes theorem

    rw [h1']
    rw [h2']

    use a * aa + b * 2 * dd + c * gg
    use a * bb + b * ee + c * hh
    use a * cc + b * 2 *  ff + c * ii
    use d * aa + e * dd + f * gg
    use 5555
    use 6555
    use 7777
    use 8888
    use 9999

    repeat rw [general_word_form]

    ext h3 h4
    fin_cases h3
    fin_cases h4
    simp
    ring_nf
    rw [Real.sq_sqrt]
    ring
    norm_num

    simp
    ring_nf

    simp
    ring_nf
    rw [Real.sq_sqrt]
    ring
    norm_num

    fin_cases h4
    simp
    ring

    simp
    repeat sorry







theorem general_word_form_h_inv : ∀ x : GL (Fin 3) Real, general_word_form_prop x n->
    general_word_form_prop (x⁻¹) n:= by
    intro x h1

    rw [general_word_form_prop] at h1
    rcases h1 with ⟨a, b, c, d, e, f, g, h, i, h1'⟩

    rw [general_word_form_prop]

    rw [@Matrix.coe_units_inv]

    rw [h1']

    use e * i - f * 2 * h
    use 2222
    use 3333
    use 4444
    use 5555
    use 6555
    use 7777
    use 8888
    use 9999

    repeat rw [general_word_form]

    rw [Matrix.inv]
    simp
    rw [adjugate_fin_three]
    simp
    rw [Matrix.det_fin_three]
    simp
    ext h3 h4
    fin_cases h3
    fin_cases h4
    simp
    ring_nf
    repeat rw [Real.sq_sqrt]
    rw [← sub_mul]
    repeat rw [← sub_mul]
    repeat sorry





theorem general_word_form_exists (x: GL (Fin 3) Real) (h1: x ∈ G) (n : Nat):
  general_word_form_prop x n :=
    Subgroup.closure_induction h1 (general_word_form_h_k n) (general_word_form_h_1 n) (general_word_form_h_mul n) (general_word_form_h_inv n)

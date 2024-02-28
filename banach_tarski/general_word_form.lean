import banach_tarski.Definitions
import Mathlib.Data.Real.Sqrt

universe u v w

variable {m : Type u} {n : Type v} {α : Type w}

theorem adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) Real) :
    Matrix.adjugate A =
    !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
      -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
      -(A 1 0 * A 2 2) + A 1 2 * A 2 0,
      A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
      A 1 0 * A 2 1 - A 1 1 * A 2 0,
      -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0] := by

    ext i j
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.updateRow, Fin.succAbove, Fin.lt_def] <;> ring


@[simp]
theorem adjugate_fin_three_of (a b c d e f g h i: Real) :
    Matrix.adjugate !![a, b, c; d, e, f; g, h, i] =
    !![e * i - f * h, -(b * i) + c * h, b * f - c * e;
     -(d * i) + f * g, a * i - c * g, -(a * f) + c * d;
      d * h - e * g, -(a * h) + b * g, a * e - b * d] :=
    adjugate_fin_three _


-- Matlab
--syms a b c d e f g h i n
--A = [(a*((1/3) ^ n)) (b * sqrt(2) * (1/3) ^ n) (c*((1/3) ^ n));
--    (d * sqrt(2) * (1/3) ^ n) (e *((1/3) ^ n)) (f * sqrt(2) * (1/3) ^ n);
--    (g*((1/3) ^ n)) (h * sqrt(2) * (1/3) ^ n) (i*((1/3) ^ n))];
--D = inv(A)


noncomputable def general_word_form  (a b c d e f g h i: ℤ) (n: Nat): Matrix (Fin 3) (Fin 3) Real :=
  !![(a : Real) * (1/3 ^ n),b * Real.sqrt 2 * (1/3 ^ n), (c : Real) * (1/3 ^ n);
    d * Real.sqrt 2 * (1/3 ^ n), (e : Real) * (1/3 ^ n), f * Real.sqrt 2 * (1/3 ^ n);
    (g: Real) * (1/3 ^ n), h * Real.sqrt 2 * (1/3 ^ n), (i : Real) * (1/3 ^ n)]



def general_word_form_prop (x: GL (Fin 3) Real)  :=
  ∃ a b c d e f g h i n, x = general_word_form a b c d e f g h i n

theorem general_word_form_h_k : ∀ x ∈ erzeuger, general_word_form_prop x := by
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




theorem general_word_form_h_1 : general_word_form_prop 1 := by
  rw [general_word_form_prop]

  sorry

theorem general_word_form_h_mul : ∀ x y : GL (Fin 3) Real, general_word_form_prop x ->
    general_word_form_prop y -> general_word_form_prop (x * y) := by
    intro x y h1 h2
    rw [general_word_form_prop] at h1
    rcases h1 with ⟨a, b, c, d, e, f, g, h, i, j, h1'⟩

    rw [general_word_form_prop] at h2
    rcases h2 with ⟨aa, bb, cc, dd, ee, ff, gg, hh, ii, jj, h2'⟩

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
    use jj + j

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




theorem general_word_form_h_inv : ∀ x : GL (Fin 3) Real, general_word_form_prop x ->
    general_word_form_prop (x⁻¹) := by
    intro x h1

    rw [general_word_form_prop] at h1
    rcases h1 with ⟨a, b, c, d, e, f, g, h, i, j, h1'⟩

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
    use j * 2

    repeat rw [general_word_form]

    rw [Matrix.inv]
    simp
    --rw [adjugate_fin_three_of]
    --simp
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







theorem general_word_form_exists (x: GL (Fin 3) Real) (h1: x ∈ G) :
  general_word_form_prop x :=
    Subgroup.closure_induction h1 general_word_form_h_k general_word_form_h_1 general_word_form_h_mul general_word_form_h_inv

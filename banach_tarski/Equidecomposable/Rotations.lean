import banach_tarski.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


noncomputable def sq_2 : Real := Real.sqrt 2

theorem pi_sqrt_two (h : ∃ x : ℚ, Real.pi = x * sq_2) : false := by
  rcases h with ⟨x, h⟩
  have h_cos : Real.cos Real.pi = -1 := by
    simp
  rw [h] at h_cos

  sorry
  --have h_cos_2 {y : ℝ}: Real.cos x = CauSeq.lim {val:=cos_taylor,property:=sorry}  := by sorry
     --(CauSeq.lim (Complex.exp' x)).re := by
  --fun (m : ℕ) => x^(2 * m)--refine (Real.ext_cauchy (?_)).symm
  --simp [Real.cos, Complex.cos, Complex.exp, Complex.exp']

  --have h_cos2 (x1:ℚ) : Real.cos x = 111
    -- google Taylorreihe https://de.wikipedia.org/wiki/Sinus_und_Kosinus#Motivation_durch_Taylorreihen

  --simp [Real.cos, Complex.cos, Complex.exp, Complex.I, CauSeq.lim,
  --  Classical.choose, Classical.indefiniteDescription]
    -- was macht das Auswahlaxiom hier??
  --fun (n : ℕ) => ∑ m in range n, => x^(2 * m) * (((-1)^

lemma sin_sqrt_2_neq_0 : Real.sin sq_2 = 0 -> false := by
  simp [Real.sin_eq_zero_iff]
  intro x h
  have hx : Real.pi = (↑x)⁻¹ * sq_2  := by
    rw [← h]
    ring_nf
    rw [mul_inv_cancel]
    simp
    --
    rw [sq_2] at h
    aesop
    have h2: Real.sqrt 2 = 0 := by
      simp [h]
    convert h2
    simp

  rw [← Bool.coe_false]
  apply pi_sqrt_two
  use (↑x)⁻¹
  simp [hx]

noncomputable def rot_sq_2 : Matrix (Fin 3) (Fin 3) Real := !![Real.cos (sq_2),-Real.sin sq_2, 0; Real.sin (sq_2), Real.cos (sq_2), 0; 0,0,1]
lemma rot_sq_2_det_ne_zero : Matrix.det rot_sq_2 ≠ 0 := by
  simp [rot_sq_2, Matrix.det_fin_three, sq_2]
  rw [@mul_self_add_mul_self_eq_zero]
  intro h1
  cases h1 with
  | intro left right =>
    rw [← Bool.coe_false]
    apply sin_sqrt_2_neq_0
    exact right


noncomputable def gl_sq_2 : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero rot_sq_2 rot_sq_2_det_ne_zero
lemma coe_gl_sq_2_eq_rot_sq_2 : ↑gl_sq_2 = rot_sq_2 := by
  rfl

------
noncomputable def rot_sq_2_inv : Matrix (Fin 3) (Fin 3) Real := !![Real.cos (sq_2), Real.sin sq_2, 0; -Real.sin (sq_2), Real.cos (sq_2), 0; 0,0,1]
lemma det_sq_2_inv_ne_zero : Matrix.det rot_sq_2_inv ≠ 0 := by
  simp [rot_sq_2_inv, Matrix.det_fin_three, sq_2]
  rw [@mul_self_add_mul_self_eq_zero]
  intro h1
  cases h1 with
  | intro left right =>
    rw [← Bool.coe_false]
    apply sin_sqrt_2_neq_0
    exact right


noncomputable def gl_sq_2_inv : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero rot_sq_2_inv det_sq_2_inv_ne_zero
lemma coe_gl_sq_2_inv_eq_rot_sq_2_inv : ↑gl_sq_2_inv = rot_sq_2_inv := by
  rfl

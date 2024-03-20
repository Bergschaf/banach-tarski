import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Rotations
import banach_tarski.Lemma_3_1



def S := {x : r_3 | (x 2) = 0 ∧ ((x 0) ^ 2 + (x 1) ^ 2 = 1)}

def A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![Real.cos (n * sq_2),Real.sin (n * sq_2),0]} -- TODO

def B : Set r_3 := (S \ {![1,0,0]}) \ A


lemma origin_not_in_A : ![1,0,0] ∉ A := by
  simp [A]
  intro x h
  refine Function.ne_iff.mpr ?_ -- TODO sehr gutes ding
  simp
  use 0
  simp
  intro h1
  symm at h1
  rw [Real.cos_eq_one_iff (x * sq_2)] at h1

  rcases h1 with ⟨a, ha⟩
  have a_nonzero : a ≠ 0 := by
    simp [sq_2] at ha
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    aesop_subst a_1
    simp_all only [Int.cast_zero, zero_mul, zero_eq_mul, Nat.cast_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
      OfNat.ofNat_ne_zero, or_false, lt_self_iff_false]

  have haa : Real.pi = (x / (2 * a)) * sq_2 := by
    rw [@div_eq_inv_mul]
    field_simp
    rw [mul_comm]
    rw [← ha]
    ring

  have haaa : ∃ q : ℚ, Real.pi = q * sq_2 := by
    use (x / (2 * a))
    simp [haa]

  rcases haaa with ⟨b, hb⟩
  rw [← Bool.coe_false]
  apply pi_sqrt_two
  use b


lemma A_and_B_eq_S : A ∪ B = S \ {![1,0,0]} := by
  simp [A, B, S, Set.subset_def]
  intro x1 x2 h1 h2
  apply And.intro
  aesop_subst h2
  simp_all only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.cos_sq_add_sin_sq, and_self]
  --
  refine Function.ne_iff.mpr ?_ -- TODO sehr gutes ding
  use 0
  simp [h2, Real.cos_eq_one_iff]
  intro x h
  rw [mul_comm] at h

  have ha : Real.pi = (x2 / (2 * x)) * sq_2 := by
    rw [@div_eq_inv_mul]
    rw [mul_assoc]
    rw [← h]
    ring_nf
    rw [mul_inv_cancel]
    simp
    --
    rw [sq_2] at h
    aesop_subst h2
    simp_all only [ne_eq, Int.cast_eq_zero]
    apply Aesop.BuiltinRules.not_intro
    intro a
    aesop_subst a
    simp_all only [Int.cast_zero, mul_zero, zero_eq_mul, Nat.cast_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
      OfNat.ofNat_ne_zero, or_false, lt_self_iff_false]

  have haa : ∃ q : ℚ, Real.pi = q * sq_2 := by
    use (x2 / ( 2 * x))
    simp [ha]

  rcases haa with ⟨b, hb⟩
  rw [← Bool.coe_false]
  apply pi_sqrt_two
  use b

lemma rotate_A_B_eq_S : rotate_set A gl_sq_2 ∪ rotate_set B gl_one = S := by
  simp [rotate_set, rotate]
  ext x
  apply Iff.intro
  simp [A, B, S, coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, coe_gl_one_eq_one]
  aesop
  simp [sq_2, neg_add_eq_sub]
  simp [@add_sq, sub_sq, mul_pow, Real.cos_sq,Real.sin_sq_eq_half_sub]
  ring
  intro h
  simp
  by_cases h1:((∃ v ∈ A, Matrix.vecMul v ↑gl_sq_2 = x))
  left
  exact h1
  --
  right
  simp [A, B, coe_gl_one_eq_one]
  apply And.intro
  apply And.intro
  . exact h
  . simp at h1
    aesop
    convert h1
    simp [coe_gl_sq_2_eq_rot_sq_2, rot_sq_2]
    use ![Real.cos sq_2 ,Real.sin sq_2,0]
    apply And.intro
    . simp [A]
      use 1
      simp
    . simp
      repeat rw [← sq]
      rw [Real.cos_sq, Real.sin_sq_eq_half_sub]
      ext i
      fin_cases i
      simp
      norm_num
      ---
      simp
      ring
      ---
      simp
  . intro x1 h2
    aesop
    simp [A] at h1
    convert h1
    simp
    use ![Real.cos ((x1 + 1) * sq_2),Real.sin ((x1 + 1) * sq_2),0]
    use x1 + 1
    simp [coe_gl_sq_2_eq_rot_sq_2, rot_sq_2]
    ext i
    fin_cases i
    simp
    rw [← Real.cos_sub]
    ring_nf
    ----
    simp
    rw [neg_add_eq_sub, ← Real.sin_sub]
    ring_nf
    ---
    simp



theorem equi_kreis : equidecomposable (S \ {![1,0,0]}) S:= by
  rw [equidecomposable]
  use [A, B]
  simp
  apply And.intro
  --
  simp [list_intersection,list_union, union, intersection,pairs, S, A, B]
  ---
  apply And.intro
  simp [list_union,union]
  exact A_and_B_eq_S
  ---
  use [gl_sq_2, gl_one]
  simp [list_union, rotate_list, union, remove_first]
  use [![0,0,0],![0,0,0]]
  simp [translate_list_zero]
  use [![0,0,0],![0,0,0]]
  save
  simp [translate_list_zero, union]
  exact rotate_A_B_eq_S

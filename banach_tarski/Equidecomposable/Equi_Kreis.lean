import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Rotations
import banach_tarski.Lemma_3_1



def S := {x : r_3 | (x 2) = 0 ∧ ((x 0) ^ 2 + (x 1) ^ 2 = 1)}

def A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![Real.cos (n * sq_2),Real.sin (n * sq_2),0]} -- TODO

def B : Set r_3 := (S \ {![1,0,0]}) \ A


lemma A_and_B_eq_S : A ∪ B = S \ {![1,0,0]} := by
  simp only [A, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt, exists_prop, B, S,
    Fin.isValue, Set.union_diff_self, Set.union_eq_right, Set.subset_def, Set.mem_diff,
    Set.mem_singleton_iff, forall_exists_index, and_imp]
  intro x1 x2 h1 h2
  apply And.intro
  aesop_subst h2
  simp_all only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.cos_sq_add_sin_sq, and_self]
  --
  refine Function.ne_iff.mpr ?_ -- TODO sehr gutes ding
  use 0
  simp only [h2, Fin.isValue, Matrix.cons_val_zero, ne_eq, Real.cos_eq_one_iff, not_exists]
  intro x h
  rw [mul_comm] at h

  have ha : Real.pi = (x2 / (2 * x)) * sq_2 := by
    rw [@div_eq_inv_mul]
    rw [mul_assoc]
    rw [← h]
    ring_nf
    rw [mul_inv_cancel]
    simp only [one_mul]
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
    simp only [ha, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast]

  rcases haa with ⟨b, hb⟩
  rw [← Bool.coe_false]
  apply pi_sqrt_two
  use b

lemma rotate_A_B_eq_S : rotate_set A gl_sq_2 ∪ rotate_set B gl_one = S := by
  simp only [rotate_set, rotate]
  ext x
  apply Iff.intro
  simp only [A, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt, exists_prop,
    coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, Matrix.vecMul_cons, Matrix.smul_cons, smul_eq_mul, mul_neg,
    mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul, add_zero, Matrix.add_cons,
    Matrix.head_cons, Matrix.tail_cons, zero_add, Matrix.empty_add_empty, B, S, Fin.isValue,
    Set.mem_diff, Set.mem_singleton_iff, not_exists, not_and, coe_gl_one_eq_one, Units.val_one,
    Matrix.vecMul_one, exists_eq_right, Set.mem_union]
  aesop
  simp only [sq_2, neg_add_eq_sub]
  simp only [add_sq, mul_pow, Real.cos_sq, one_div, Real.sin_sq_eq_half_sub, sub_sq]
  ring
  intro h
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_cases h1:((∃ v ∈ A, Matrix.vecMul v ↑gl_sq_2 = x))
  . left
    exact h1

  . right
    simp only [B, A, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt, exists_prop,
      Set.mem_diff, Set.mem_singleton_iff, not_exists, not_and, coe_gl_one_eq_one, Units.val_one,
      Matrix.vecMul_one, exists_eq_right]
    apply And.intro
    apply And.intro
    . exact h
    . simp only [not_exists, not_and] at h1
      aesop
      convert h1
      simp only [coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, Matrix.vecMul_cons, Matrix.smul_cons,
        smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul, add_zero,
        Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, zero_add, Matrix.empty_add_empty,
        false_iff, not_forall, not_not, exists_prop]
      use ![Real.cos sq_2 ,Real.sin sq_2,0]
      apply And.intro
      . simp only [A, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt, exists_prop]
        use 1
        simp only [zero_lt_one, Nat.cast_one, one_mul, and_self]
      . simp only [Matrix.head_cons, Matrix.tail_cons]
        repeat rw [← sq]
        rw [Real.cos_sq, Real.sin_sq_eq_half_sub]
        ext i
        fin_cases i <;> simp only [one_div, add_add_sub_cancel, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] <;> norm_num
        ring

    . intro x1 h2
      aesop
      simp only [A, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, gt_iff_lt, exists_prop,
        forall_exists_index, and_imp] at h1
      convert h1
      simp only [false_iff, not_forall, not_not, exists_prop, exists_and_left]
      use ![Real.cos ((x1 + 1) * sq_2),Real.sin ((x1 + 1) * sq_2),0]
      use x1 + 1
      simp only [add_pos_iff, zero_lt_one, or_true, Nat.cast_add, Nat.cast_one,
        coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, Matrix.vecMul_cons, Matrix.head_cons, Matrix.smul_cons,
        smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty, Matrix.tail_cons, zero_smul,
        Matrix.empty_vecMul, add_zero, Matrix.add_cons, Matrix.empty_add_empty, true_and]
      ext i
      fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [← Real.cos_sub]
      ring_nf
      ----
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      rw [neg_add_eq_sub, ← Real.sin_sub]
      ring_nf
      ---
      simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem equi_kreis : equidecomposable (S \ {![1,0,0]}) S:= by
  rw [equidecomposable]
  use [A, B]
  simp only [List.length_cons, List.length_singleton, Set.coe_setOf, Nat.reduceSucc,
    Set.mem_setOf_eq, exists_and_left, Subtype.exists]
  apply And.intro
  --
  simp only [list_intersection, list_union, pairs, A, Set.coe_setOf, Set.mem_setOf_eq,
    Subtype.exists, gt_iff_lt, exists_prop, B, S, Fin.isValue, List.map_cons, List.map_nil,
    List.append_nil, List.singleton_append, intersection, Set.inter_diff_self, List.foldl_cons,
    union, Set.union_self, List.foldl_nil]
  ---
  apply And.intro
  simp only [list_union, List.foldl_cons, union, Set.empty_union, List.foldl_nil]
  exact A_and_B_eq_S
  ---
  use [gl_sq_2, gl_one]
  simp_all only [list_union, List.length_nil, Nat.reduceSucc, rotate_list, List.head_cons, remove_first,
    List.tail_cons, List.length_cons, List.length_singleton, exists_true_left]
  use [![0,0,0],![0,0,0]]
  simp_all only [List.length_cons, List.length_nil, exists_true_left]
  use [![0,0,0],![0,0,0]]
  simp [translate_list_zero, union]
  exact rotate_A_B_eq_S

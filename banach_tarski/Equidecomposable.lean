import Mathlib.Data.List.Basic

import banach_tarski.Definitions
import banach_tarski.Lemma_3_1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational

import Mathlib.Data.Finset.Basic


def intersection (α : Type) (a : Set α × Set α): Set α := a.1 ∩ a.2

def union (α : Type) (a b : Set α) :Set α := a ∪ b

def list_union (α : Type) (x : List (Set α)): Set α :=
  x.foldl (union α) ∅

def len_gt_one {α : Type} (l : List (Set α)) : Prop := 1 < l.length

def pairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

def list_intersection (α : Type) (x : List (Set α)): Set α :=
  list_union α ((pairs x).map (intersection α))

def rotate_set (x : Set r_3) (p : GL (Fin 3) Real) : Set r_3 :=
  {w : r_3  | ∃ v, v ∈ x -> rotate p v = w}


-- Define a function to remove the first element of a list
def remove_first {α : Type} (x : List α ):List α :=
  x.tail

lemma remove_first_length_eq {a: Type} {n: Nat} (x : List α ) (h_n: n = x.length): (remove_first x).length = n - 1 := by
  rw [remove_first]
  simp
  rw [h_n]

variable (n : Nat)

def rotate_list (n : Nat) (x : List (Set r_3)) (p : List (GL (Fin 3) Real)) (h_n: n = x.length) (h : x.length = p.length): List (Set r_3) :=
  -- n eq list.length
  match n with
  | 0 => []
  --| 1 => [rotate_set (x.head (List.length_pos.mp h1)) (p.head (List.length_pos.mp h2))]
  | (Nat.succ m) =>
      have h_new : (remove_first x).length = (remove_first p).length := by
        rw [remove_first]
        rw [remove_first]
        simp
        rw [h]

      have h_n_new : m = (remove_first x).length := by
        rw [remove_first]
        simp
        exact eq_tsub_of_add_eq h_n

      have h1 : 0 < x.length :=  by
        exact (Nat.mem_range_succ (List.length x)).mp (Exists.intro m h_n)

      have h2: 0 < p.length := by
        rw [← h]
        exact h1

      rotate_set (x.head (List.length_pos.mp h1)) (p.head (List.length_pos.mp h2))
                    :: rotate_list m (remove_first x) (remove_first p) h_n_new h_new


def equidecomposable (X Y : Set r_3) : Prop :=
  ∃ Parts_X : List (Set r_3),∃ g_s : {w : List (GL (Fin 3) Real) | w.length = Parts_X.length}, list_intersection r_3 Parts_X = ∅ ∧
  list_union r_3 Parts_X = X ∧
   list_union r_3 (rotate_list Parts_X.length Parts_X g_s (by simp)  (by simp)) = Y

/--blueprint-/
--lemma equidecomposable_self (X : Set r_3) : equidecomposable X X := by
--  simp [equidecomposable, list_intersection]
--  use [X]
--  simp [list_union,]
--  sorry


lemma equidecomposable_subset (X Y : Set r_3) (X₁ X₂ Y₁ Y₂ : Set r_3)
  (hx_union : X₁ ∪ X₂ = X) (hx_intersection : X₁ ∩ X₂ = ∅) (hy_union : Y₁ ∪ Y₂ = Y)
  (hy_intersection : Y₁ ∩ Y₂ = Y) (hxy_eq : X₁ = Y₁) (h_equi : equidecomposable X₂ Y₂):
    equidecomposable X Y := by
  simp [equidecomposable]
  simp [equidecomposable] at h_equi
  rcases h_equi with ⟨a, ha⟩
  use [X₁] ++ a
  cases ha with
  | intro ha1 ha2 =>
  cases ha2 with
  | intro ha2 ha3 =>
  rcases ha3 with ⟨rot, ha3⟩
  rcases ha3 with ⟨ha4, ha3⟩

  apply And.intro
  simp [union, intersection, pairs]
  sorry
  --
  apply And.intro
  sorry
  --
  use gl_one::rot
  simp
  use ha4
  sorry

--- Äqui Kreis
noncomputable def sq_2 : Real := Real.sqrt 2


--noncomputable def cos_taylor_series (x : ℝ) (n : ℕ ):=
  -- google Taylorreihe https://de.wikipedia.org/wiki/Sinus_und_Kosinus#Motivation_durch_Taylorreihen
--  (-1) ^ n * (x ^ (2 * n) / Nat.factorial (2 * n)) + cos_taylor_series x (n)




noncomputable def cos_taylor (n: ℕ) (x : ℝ) := Finset.sum (Finset.range n) (fun (m : ℕ ) => x^(2 * m) * (((-1)^m) / Nat.factorial (2 * m)))

#check cos_taylor

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
    aesop
    simp [sq_2] at h_1

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

lemma all_A_different : ∀ n m : {x : ℕ | x > 0},n ≠ m ->  ![Real.cos (n * sq_2),Real.sin (n * sq_2),0] ≠ ![Real.cos (m * sq_2),Real.sin (m * sq_2),0] := by
  simp
  intro n hn m hm h_nm
  refine Function.ne_iff.mpr ?_ -- TODO sehr gutes ding
  use 0
  simp

  sorry


theorem A_countable : Countable A := by
  sorry


/--
Neue Beweisidee
A = {Alle punkte auf dem Kreis im abstand von sqrt 2 ohne [1,0]}
Wir rotieren A um den Urprung um (- sqrt 2) Einheiten -> A'
der erste Punkt aus A wird auf [1,0] abgebildet
alle punkte aus A sind in A'
-/
noncomputable def rot_sq_2 : Matrix (Fin 3) (Fin 3) Real := !![Real.cos (-sq_2),-Real.sin sq_2, 0; Real.sin (-sq_2), Real.cos (-sq_2), 0; 0,0,1]
lemma rot_sq_2_det_ne_zero : Matrix.det rot_sq_2 ≠ 0 := by
  simp [rot_sq_2, Matrix.det_fin_three, sq_2]
  rw [← Real.cos_add]
  sorry
noncomputable def gl_sq_2 : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero rot_sq_2 rot_sq_2_det_ne_zero
lemma coe_gl_sq_2_eq_rot_sq_2 : ↑gl_sq_2 = rot_sq_2 := by
  rfl

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
  have ha : Real.pi = (x2 / (2 * x)) * sq_2 := by
    rw [@div_eq_inv_mul]
    field_simp
    rw [mul_comm]
    sorry
  sorry -- to lazy, proof ist definitely possible

lemma rotate_A_B_eq_S : rotate_set A gl_sq_2 ∪ rotate_set B gl_one = S := by
  simp [rotate_set, rotate]
  ext X
  apply Iff.intro
  simp [A, B, S, coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, coe_gl_one_eq_one]








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
  exact rotate_A_B_eq_S


  /-
  simp [list_union, union, A, B, S, rotate_list, rotate_set, remove_first, rotate]
  use [gl_sq_2, gl_one]
  simp
  simp [coe_gl_sq_2_eq_rot_sq_2, rot_sq_2, coe_gl_one_eq_one]
  refine (Set.ext ?h.h).symm
  intro x
  simp
  apply Iff.intro
  --
  intro a
  simp_all only [Matrix.head_cons, Matrix.tail_cons]
  unhygienic with_reducible aesop_destruct_products
  apply Or.inr
  apply Exists.intro
  intro a a_1 a_2 a_3
  apply Eq.refl
  ---

  intro h
  cases h with
  | inl h =>
    rcases h with ⟨x1, h⟩
    apply equi_kreis_case_inl

  | inr h => sorry-/

def Kreis_in_Kugel : Set r_3 := {p : r_3 | ((2 * (p 0) - 1)) ^ 2 + (2 * (p 1)) ^ 2 = 1 ∧ p 2 = 0}
def Kreis_in_Kugel_ohne_Origin : Set r_3 := Kreis_in_Kugel \ {origin}

lemma Kreis_subset_L : Kreis_in_Kugel ⊆ L := by
  simp [Kreis_in_Kugel, L]
  intro a ha1 ha2

  sorry

lemma origin_in_kreis : origin ∈ Kreis_in_Kugel := by
  simp [origin, Kreis_in_Kugel]


theorem equi_kugel : equidecomposable L L' := by
  sorry

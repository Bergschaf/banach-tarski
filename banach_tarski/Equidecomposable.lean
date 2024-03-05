import Mathlib.Data.List.Basic

import banach_tarski.Definitions
import banach_tarski.Lemma_3_1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational

--def get_pair {α : Type} (l : List α) (h: 1 < l.length): (α × α) := (l.get {val:=0, isLt:=by exact Nat.zero_lt_of_lt h}, l.get {val:=1, isLt:=h})

--def unique_pairs {α : Type} (l : List α) : List (α × α) :=
--  match l.length with
--  | 0 => []
--  | 1 => []
--  | n => l.permutations.map get_pair

def intersection (α : Type) (a : (Set α × Set α)) :Set α := a.1 ∩ a.2

def union (α : Type) (a b : Set α) :Set α := a ∪ b

def list_union (α : Type) (x : List (Set α)): Set α :=
  x.foldl (union α) ∅

def list_intersection (α : Type) (x : List (Set α)) (X : Set α): Set α :=
  list_union α ((x.product x).map (intersection α)) -- false


def rotate_set (x : Set r_3) (p : GL (Fin 3) Real): Set r_3 :=
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


--def equidecomposable (X Y : Set r_3) :=
--  ∃ Parts_X,list_intersection r_3 Parts_X X = ∅ →
--  list_union r_3 Parts_X = X →
--  ∃ g_s, (h_eq : Parts_X.length = g_s.length) → (h_n: Parts_X.length = Parts_X.length) → list_union r_3 (rotate_list Parts_X.length Parts_X g_s h_n h_eq) = Y

-- TODO list intersection has to check pairwise
def equidecomposable (X Y : Set r_3) : Prop :=
  ∃ Parts_X : List (Set r_3),∃ g_s : {w : List (GL (Fin 3) Real) | w.length = Parts_X.length}, list_intersection r_3 Parts_X X = ∅ ∧
  list_union r_3 Parts_X = X ∧
   list_union r_3 (rotate_list Parts_X.length Parts_X g_s (by simp)  (by simp)) = Y

/--blueprint-/
lemma equidecomposable_self (X : Set r_3) : equidecomposable X X := by
  simp [equidecomposable, list_intersection]
  use [X]
  simp [list_union,]


lemma equidecomposable_subset (X Y : Set r_3) :
  ∃ X₁ X₂ Y₁ Y₂, X₁ ∪ X₂ = X -> Y₁ ∪ Y₂ = Y -> X₁ = Y₁ -> equidecomposable X₂ Y₂ ->
    equidecomposable X Y := by sorry


--- Äqui Kreis
noncomputable def sq_2 : Real := Real.sqrt 2


theorem pi_sqrt_two (h : ∃ x : ℚ, Real.pi = x * sq_2) : false := by
  simp
  absurd h
  simp
  aesop
  absurd h_1
  sorry
  simp [sq_2] at h


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

theorem equi_kreis : equidecomposable (S \ {![1,0,0]}) S:= by
  rw [equidecomposable]
  use [A, B]
  simp
  apply And.intro
  --
  simp [list_intersection, intersection, S, A, B]
  sorry -- TODO this is all true, but just takes long to compile
  --unhygienic ext
  --simp_all only [Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, not_exists, not_and,
  --  Set.mem_empty_iff_false, iff_false, and_self, not_false_eq_true, true_and, not_forall, not_not, exists_prop,
  --  and_imp, forall_exists_index, implies_true, forall_const]
  ---
  apply And.intro
  simp [list_union, union, A, B, S]
  sorry
  ---
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
  sorry


theorem equi_kugel : equidecomposable L L' := by
  rw [equidecomposable]

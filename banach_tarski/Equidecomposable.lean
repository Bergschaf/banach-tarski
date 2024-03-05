import Mathlib.Data.List.Basic

import banach_tarski.Definitions
import banach_tarski.Lemma_3_1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational

def intersection (α : Type) (a b:Set α) :Set α := a ∩ b

def list_intersection (α : Type) (x : List (Set α)) (X : Set α): Set α :=
  x.foldl (intersection α) X


def union (α : Type) (a b : Set α) :Set α := a ∪ b

def list_union (α : Type) (x : List (Set α)): Set α :=
  x.foldl (union α) ∅


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

def rotate_list (n : Nat) (x : List (Set r_3)) (p : List G) (h_n: n = x.length) (h : x.length = p.length): List (Set r_3) :=
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


def equidecomposable (X Y : Set r_3) :=
  ∃ Parts_X,list_intersection r_3 Parts_X X = ∅ →
  list_union r_3 Parts_X = X →
  ∃ g_s, (h_eq : Parts_X.length = g_s.length) → (h_n: Parts_X.length = Parts_X.length) → list_union r_3 (rotate_list Parts_X.length Parts_X g_s h_n h_eq) = Y


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

theorem equi_kreis : equidecomposable S (S \ {![1,0,0]}) := by
    sorry



theorem equi_kugel : equidecomposable L L' := by
  sorry

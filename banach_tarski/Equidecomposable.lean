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


theorem pi_sqrt_two : ¬ (∃ x : ℚ, Real.pi = x * sq_2) := by
  simp
  intro h1

  intro h2
  sorry



def S := {x : r_3 | (x 2) = 0 ∧ ((x 0) ^ 2 + (x 1) ^ 2 = 1)}


def A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![Real.cos (n * sq_2),Real.sin (n * sq_2),0]} -- TODO

def B : Set r_3 := (S \ {![1,0,0]}) \ A

lemma sqrt_two_mul_pos_nat_neq_1: ¬ (∃ n : {x : ℕ | x > 0} , Real.cos (n * sq_2) = 1) := by
  simp [sq_2]
  intro m
  rw [← ne_eq]
  intro h

  apply Irrational.ne_one
  sorry

lemma origin_not_in_A : ![1,0,0] ∉ A := by
  simp [A]
  sorry




/--
Neue Beweisidee
A = {Alle punkte auf dem Kreis im abstand von sqrt 2 ohne [1,0]}
Wir rotieren A um den Urprung um (- sqrt 2) Einheiten -> A'
der erste Punkt aus A wird auf [1,0] abgebildet
alle punkte aus A sind in A'
-/
theorem equi_kreis : equidecomposable S (S \ {![1,0,0]}) := by
    simp [equidecomposable]
    sorry

theorem equi_kugel : equidecomposable L L' := by
  sorry

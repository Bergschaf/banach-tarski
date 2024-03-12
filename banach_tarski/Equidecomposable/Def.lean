import Mathlib.Data.List.Basic

import banach_tarski.Definitions

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Irrational

import Mathlib.Data.Finset.Basic


def intersection (α : Type) (a : Set α × Set α): Set α := a.1 ∩ a.2

def union (α : Type) (a b : Set α) :Set α := a ∪ b

def list_union (α : Type) (x : List (Set α)): Set α :=
  x.foldl (union α) ∅

def pairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

def list_intersection (α : Type) (x : List (Set α)): Set α :=
  list_union α ((pairs x).map (intersection α))

def translate_set (x : Set r_3) (p : r_3) : Set r_3 :=
  {w : r_3  | ∃ v, v ∈ x ∧ translate p v = w}

lemma translate_zero (x : r_3) : translate ![0,0,0] x = x := by
  simp [translate]
  exact List.ofFn_inj.mp rfl

lemma translate_set_zero (x : Set r_3) : translate_set x ![0,0,0] = x := by
  simp [translate_set, translate_zero]


def remove_first {α : Type} (x : List α) : List α :=
  x.tail

lemma remove_first_length_eq {a: Type} {n: Nat} (x : List α ) (h_n: n = x.length): (remove_first x).length = n - 1 := by
  rw [remove_first]
  simp
  rw [h_n]

variable (n : Nat)

def rotate_list (n : Nat) (x : List (Set r_3)) (p : List (GL (Fin 3) Real)) (h_n: n = x.length) (h : x.length = p.length): List (Set r_3) :=
  match n with
  | 0 => []
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

lemma rotate_list_length_cons (n : Nat) (x : List (Set r_3)) (p : List (GL (Fin 3) Real)) (h_n: n = x.length) (h : x.length = p.length) :
  List.length (rotate_list n x p h_n h) = n := by
  induction n generalizing x p with
  | zero => simp [rotate_list]
  | succ n ih =>
    simp [rotate_list]
    have h_n_new : n = List.length (remove_first x) := by
      simp [remove_first,← h_n]
    have h_new : List.length (remove_first x) = List.length (remove_first p) := by
      simp [remove_first, h]

    specialize ih (remove_first x) (remove_first p) (h_n_new) (h_new)
    apply ih

def translate_list (n : Nat) (x : List (Set r_3)) (p : List r_3) (h_n: n = x.length) (h : x.length = p.length): List (Set r_3) :=
  match n with
  | 0 => []
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

      translate_set (x.head (List.length_pos.mp h1)) (p.head (List.length_pos.mp h2))
                    :: translate_list m (remove_first x) (remove_first p) h_n_new h_new

lemma translate_list_zero (n : Nat) (x : List (Set r_3)) (p : List r_3) (h_n: n = x.length) (h : x.length = p.length)
  (h0: ∀ y ∈ p, y = ![0,0,0]) : translate_list n x p h_n h = x := by
  induction n generalizing x p with
  | zero =>
    simp [translate_list]
    exact List.IsInfix.eq_of_length (Exists.intro [] (Exists.intro x rfl)) h_n
  | succ n ih =>
    simp [translate_list]
    have h_p_nonempty : p ≠ [] := by
      rename_i n_1
      simp_all only [ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      aesop_subst a
      simp_all only [List.length_nil, Nat.succ_ne_zero]

    have h_p_head_zero : List.head p h_p_nonempty = ![0,0,0] := by
      apply h0
      exact List.head_mem h_p_nonempty

    have h_0_new : ∀ y ∈ (remove_first p), y = ![0,0,0] := by
      simp [remove_first]
      intro y hy
      apply h0
      exact List.mem_of_mem_tail hy

    rw [h_p_head_zero]
    rw [translate_set_zero]
    specialize ih (remove_first x) (remove_first p) (by simp [remove_first, ← h_n])
       (by simp[remove_first,h]) (h_0_new)
    rw [ih]
    simp [remove_first]
    refine (List.eq_cons_of_mem_head? (?_)).symm
    apply List.head?_eq_head

def equidecomposable (X Y : Set r_3) : Prop :=
  ∃ Parts_X : List (Set r_3),∃ g_s : {w : List (GL (Fin 3) Real) | w.length = Parts_X.length},∃ translations : {w : List r_3 | w.length = Parts_X.length}, list_intersection r_3 Parts_X = ∅ ∧
  list_union r_3 Parts_X = X ∧
   list_union r_3 (translate_list Parts_X.length (rotate_list Parts_X.length Parts_X g_s (by simp)  (by simp)) translations (by simp [rotate_list_length_cons]) (by simp [rotate_list_length_cons])) = Y

/--blueprint-/
--lemma equidecomposable_self (X : Set r_3) : equidecomposable X X := by
--  simp [equidecomposable, list_intersection]
--  use [X]
--  simp [list_union,]
--  sorry
--def equidecomposable_trans {X Y Z: Set r_3} (h1 : )

lemma list_intersection_list {α : Type} (X : Set α) (a : List (Set α)) (h1 : list_intersection α a = ∅) (h2 : list_union α a ∩ X = ∅) :
  list_intersection α (X::a) = ∅ := by
  simp [list_intersection] at *
  sorry


lemma equidecomposable_subset (X Y : Set r_3) (X₁ X₂ Y₁ Y₂ : Set r_3)
  (hx_union : X₁ ∪ X₂ = X) (hx_intersection : X₁ ∩ X₂ = ∅) (hy_union : Y₁ ∪ Y₂ = Y)
  (hy_intersection : Y₁ ∩ Y₂ = ∅) (hxy_eq : X₁ = Y₁) (h_equi : equidecomposable X₂ Y₂):
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
  rcases ha3 with ⟨translations, ha3⟩
  rcases ha3 with ⟨ha5, ha3⟩

  apply And.intro
  . simp
    apply list_intersection_list
    exact ha1
    rw [ha2]
    rw [← hx_intersection]
    exact Set.inter_comm X₂ X₁

  --
  apply And.intro
  . simp only [list_union, List.singleton_append, List.foldl_cons, union, Set.empty_union]
    rw [← hx_union]
    rw [← ha2]
    rw [list_union]
    sorry
  --
  use gl_one::rot
  simp
  use ha4
  sorry

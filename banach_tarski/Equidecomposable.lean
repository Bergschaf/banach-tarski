import Mathlib.Data.List.Basic

import banach_tarski.Definitions
import banach_tarski.Lemma_3_1


def intersection (α : Type) (a b:Set α) :Set α := a ∩ b

def list_intersection (α : Type) (x : List (Set α)) (X : Set α): Set α :=
  x.foldl (intersection α) X


def union (α : Type) (a b:Set α) :Set α := a ∪ b

def list_union (α : Type) (x : List (Set α)): Set α :=
  x.foldl (union α) ∅


def rotate_set (x : Set r_3) (p : GL (Fin 3) Real): Set r_3 :=
  {w : r_3  | ∃ v, v ∈ x -> rotate p v = w}


-- Define a function to remove the first element of a list
def remove_first {α : Type} (x : List α ):List α :=
  match  x with
  | []       => []
  | (x::xs)  => xs

def rotate_list_wrapper (x : List (Set r_3)) (p : List G) : List (Set r_3) :=
  sorry

def rotate_list (n : Nat) (x : List (Set r_3)) (p : List G) (h_n: n = x.length) (h : x.length = p.length) (h1 : 0 < x.length): List (Set r_3) :=
  -- n eq list.length
  have h2 : 0 < p.length := by
    exact Nat.lt_of_lt_of_eq h1 h
  match n with
  | 0 => []
  | 1 => [rotate_set (x.head (List.length_pos.mp h1)) (p.head (List.length_pos.mp h2))]
  | (Nat.succ m) =>
      have h_new : (remove_first x).length = (remove_first p).length := by
        sorry

      have h_n_new : m = (remove_first x).length := by
        sorry

      have h1_new : 0 < (remove_first x).length := by
        sorry

      rotate_set (x.head (List.length_pos.mp h1)) (p.head (List.length_pos.mp h2))
                    :: rotate_list m (remove_first x) (remove_first p) h_n_new h_new h1_new


def equidecomposable (X Y : Set r_3) :=
  ∃ Parts_X, list_intersection r_3 Parts_X X = ∅ →
  list_union r_3 Parts_X = X →
  ∃ g_s, g_s.length = Parts_X.length → list_union r_3 (rotate_list_wrapper Parts_X g_s) = Y

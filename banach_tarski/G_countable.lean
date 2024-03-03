import banach_tarski.Definitions

-- the fact that g is a free group should prove that it is countable
def item_to_int (i : erzeuger_t × Bool) : Nat :=
  match i with
  | (erzeuger_t.gl_a, true) => 1
  | (erzeuger_t.gl_a, false) => 2
  | (erzeuger_t.gl_b, true) => 3
  | (erzeuger_t.gl_b, false) => 4


def map_G_to_Nat (w :  List (erzeuger_t × Bool)) : Nat :=
  match w with
  | [] => 0
  | (head::rest) => item_to_int head + 10 * map_G_to_Nat rest


lemma map_G_empty_eq_empty : map_G_to_Nat [] = 0 := by
  exact rfl

lemma empty_eq_map_empty (a1 : List (erzeuger_t × Bool)) : map_G_to_Nat a1 = 0 -> a1 = [] := by
  intro h1
  rw [@List.eq_nil_iff_forall_not_mem]
  simp
  intro a
  sorry
  --cases a


lemma g_countable : Function.Injective map_G_to_Nat := by
  rw [Function.Injective]
  intro a1 a2
  induction a1 generalizing a2 with
  | nil =>
    simp [map_G_to_Nat]
    induction a2 with
    | nil => simp
    | cons head tail ih =>
      simp
      cases head with
      | mk fst snd =>
        cases fst
        cases snd
        simp [map_G_to_Nat, item_to_int]
        ring_nf
        sorry
        sorry
        sorry


  | cons head tail ih =>
    sorry

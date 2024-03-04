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
        repeat
          simp [map_G_to_Nat, item_to_int]
          rw [← ne_eq]
          rw [ne_iff_lt_or_gt]
          simp
        cases snd
        simp [map_G_to_Nat, item_to_int]
        left
        simp

  | cons head tail ih =>
    --simp [map_G_to_Nat, item_to_int]
    --simp [map_G_to_Nat, item_to_int]
    induction a2 with
    | nil =>
      simp [map_G_to_Nat, item_to_int]
      cases head with
      | mk fst snd =>
        cases fst <;> cases snd <;> simp

    | cons head1 tail1 ih1 =>
      induction tail with
      | nil => sorry
      | cons head tail ih => sorry






def f := "Hello WOrld"


    /-
      cases head with
      | mk fst snd =>
        cases head1 with
        | mk fst1 snd1 =>
          cases fst
          cases fst1
          cases snd
          cases snd1
          simp [map_G_to_Nat, item_to_int]
          simp [map_G_to_Nat, item_to_int] at h
          simp [map_G_to_Nat, item_to_int] at ih1
          rw [ih]
          exact h
          -------
          --specialize @ih tail1
          specialize @ih1 tail1


          simp [map_G_to_Nat, item_to_int] at h
          simp [map_G_to_Nat, item_to_int] at ih1
          --rw [ih1]
          rw [ih]
          rw [ih1]









    /-
    cases head with
    | mk fst snd =>
      cases fst
      cases snd
      intro h
      --specialize ih
      rw [ih rfl]
      repeat sorry
      --- TODO use something in the FreeGroup file that proves this-/

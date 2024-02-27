import Mathlib.GroupTheory.FreeGroup.Basic

inductive Erzeuger
  | a : Erzeuger
  | b : Erzeuger
  deriving DecidableEq, Repr


abbrev G := FreeGroup Erzeuger

def S_A := {w : G | (FreeGroup.toWord w).head? = (Erzeuger.a, true)}
def S_A' := {w : G | (FreeGroup.toWord w).head? = (Erzeuger.a, false)}
def S_B := {w : G | (FreeGroup.toWord w).head? = (Erzeuger.b, true)}
def S_B' := {w : G | (FreeGroup.toWord w).head? = (Erzeuger.b, false)}

def test_list := [(Erzeuger.a, true),(Erzeuger.a, true),(Erzeuger.a, false)]

#eval test_list
#eval FreeGroup.reduce test_list

def append_to_word (w : G) (a : (Erzeuger × Bool)) : G :=
   w * (FreeGroup.mk [a])

def append_to_all (g : Set G) (a : (Erzeuger × Bool)) : Set G :=
  {w : G | ∃ ww : g, append_to_word ww a = w}

def inv_letter (l : (Erzeuger × Bool)) :=
  (l.fst,not l.snd)

def word_head (w : G) : Option (Erzeuger × Bool) := (FreeGroup.toWord w).head?

def word_length (w : G) : Nat := w.toWord.length

def word_head_len (w : G) (h1 : word_length w > 0) : (Erzeuger × Bool) :=
  have h : (FreeGroup.toWord w) ≠ [] := by
    exact List.length_pos.mp h1
  (FreeGroup.toWord w).head h

lemma x_geq_two_eq_x_g_one {x : Nat } (h: x >= 2) : x > 0 := by
  exact Nat.zero_lt_of_lt h

theorem not_inv_after_head (w : G) (h : (Erzeuger × Bool)) (h2: word_length w >= 2) (h1 : word_head_len w (x_geq_two_eq_x_g_one h2) = h) :
  (FreeGroup.toWord w).get ({val:=1,isLt:=h2} : Fin (FreeGroup.toWord w).length) ≠ inv_letter h := by
  simp
  rw [inv_letter]









theorem append_head_cancel (w : G) (h : (Erzeuger × Bool)) (h1 : word_head w = h) :
  word_head (append_to_word w (inv_letter h)) ≠ inv_letter h := by
  rw [word_head]
  rw [inv_letter]
  rw [append_to_word]
  simp
  sorry


theorem banach_tarski : (append_to_all S_A (Erzeuger.a, false)) = S_A ∪ S_B ∪ S_B' := by
  rw [append_to_all, S_A, S_B, S_B']

  simp only [Subtype.exists, exists_prop]
  refine Set.ext_iff.mpr ?_
  intro x
  simp
  --rw [FreeGroup.toWord]

  apply Iff.intro

  intro h1

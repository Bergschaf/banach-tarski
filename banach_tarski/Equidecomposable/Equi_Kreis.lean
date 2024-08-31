import banach_tarski.Equidecomposable.Def
import banach_tarski.Equidecomposable.Rotations
--import banach_tarski.Lemma_3_1





def S : Set r_3 := {x : r_3 | (x 2) = 0 ∧ ((x 0) ^ 2 + (x 1) ^ 2 = 1)}

def A : Set r_3 := {w : r_3 | ∃ n : {x : ℕ | x > 0}, w = ![Real.cos (n * sq_2),Real.sin (n * sq_2),0]} -- TODO

def B : Set r_3 := (S \ {![1,0,0]}) \ A



theorem Equidecomposable_S_B : Equidecomposable S B := by
  sorry

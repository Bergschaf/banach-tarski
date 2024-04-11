--import banach_tarski.Lemma_3_1
--import banach_tarski.Lemma_3_2
--import banach_tarski.Equidecomposable.Equi_Kreis
--import banach_tarski.Equidecomposable.Equi_Ball
--import banach_tarski.Orbit
--import LeanCopilot

--import LeanCopilot
import LLMlean
def sum_up_to (n : Nat): Nat :=
  match n with
    | 0 => 0
    | (Nat.succ n) => sum_up_to n + Nat.succ n

#eval sum_up_to 10

theorem kleiner_gauss (n: Nat) :
  sum_up_to n * 2 = n * (n + 1) := by
  llmstep ""

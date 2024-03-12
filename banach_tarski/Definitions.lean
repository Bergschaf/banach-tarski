import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

import Mathlib.Topology.MetricSpace.PseudoMetric

import Mathlib.GroupTheory.FreeGroup.Basic

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
set_option maxHeartbeats 0


noncomputable section
def matrix_a   : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, -2/3*Real.sqrt 2; 0, 2/3*Real.sqrt 2, 1/3]
def matrix_a'  : Matrix (Fin 3) (Fin 3) Real := !![1, 0, 0; 0, 1/3, 2/3*Real.sqrt 2; 0, -2/3*Real.sqrt 2, 1/3]
def matrix_b   : Matrix (Fin 3) (Fin 3) Real := !![1/3, -2/3*Real.sqrt 2, 0; (2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_b'  : Matrix (Fin 3) (Fin 3) Real := !![1/3, 2/3*Real.sqrt 2, 0; (-2/3*Real.sqrt 2), 1/3, 0; 0, 0, 1]
def matrix_one : Matrix (Fin 3) (Fin 3) Real := 1
end noncomputable section

theorem matrix_a_inverse :  matrix_a * matrix_a' = matrix_one := by
  rw [matrix_a]
  rw [matrix_a']
  rw [matrix_one]
  norm_num
  ext h1 h2
  fin_cases h1
  simp
  rw [@Matrix.one_fin_three]
  simp

  simp
  norm_num
  rw [@mul_mul_mul_comm]
  norm_num
  simp
  rw [div_eq_mul_inv]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [@Mathlib.Tactic.RingNF.add_neg]
  rw [@mul_assoc]
  rw [mul_comm 3⁻¹]
  rw [mul_comm 3⁻¹]
  rw [← mul_assoc]
  rw [sub_self]
  rw [@Matrix.one_fin_three]
  simp

  simp
  ring_nf
  simp
  ring_nf
  rw [@Matrix.one_fin_three]
  exact rfl

theorem matrix_a_det_neq_zero : Matrix.det matrix_a ≠ 0 := by
  rw [matrix_a]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_a'_det_neq_zero : Matrix.det matrix_a' ≠ 0 := by
  rw [matrix_a']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_b_det_neq_zero : Matrix.det matrix_b ≠ 0 := by
  rw [matrix_b]
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_b'_det_neq_zero : Matrix.det matrix_b' ≠ 0 := by
  rw [matrix_b']
  rw [Matrix.det_fin_three]
  simp
  norm_num
  ring_nf
  simp
  norm_num

theorem matrix_one_det_neq_zero : Matrix.det matrix_one ≠ 0 := by
  rw [matrix_one]
  rw [Matrix.det_fin_three]
  simp
  repeat rw [Matrix.one_apply_ne]
  norm_num
  rw [@ne_iff_lt_or_gt]
  simp
  exact Fin.ne_of_lt (Nat.le.step Nat.le.refl)
  exact Fin.ne_of_gt Nat.le.refl
  exact Fin.ne_of_lt Nat.le.refl


noncomputable section
def gl_a   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a matrix_a_det_neq_zero
def gl_a'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_a' matrix_a'_det_neq_zero
def gl_b   : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b matrix_b_det_neq_zero
def gl_b'  : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_b' matrix_b'_det_neq_zero
def gl_one : GL (Fin 3) Real := Matrix.GeneralLinearGroup.mkOfDetNeZero matrix_one matrix_one_det_neq_zero
end noncomputable section


def erzeuger : Set (GL (Fin 3) Real) := {gl_a, gl_b}

def G := Subgroup.closure erzeuger


abbrev r_3 := Fin 3 -> ℝ
abbrev r_2 := Fin 2 -> ℝ
def zero_one_zero : r_3 := ![0,1,0]

def rotate (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  (p : Matrix (Fin 3) (Fin 3) Real).vecMul vec

def rotate_n_times (n : ℕ) (p : GL (Fin 3) Real) (vec : r_3) : r_3 :=
  match n with
  | 0 => vec
  | Nat.succ m => rotate_n_times m p (rotate p vec)

def translate (p : r_3) (vec : r_3) : r_3 := p + vec

def L := {w : r_3 | Real.sqrt (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) + w 2 ^ 2 ≤ 1}
def origin : r_3 := ![0,0,0]
def L' := L \ {origin}

def fixpunkt (y: r_3) (p: GL (Fin 3) Real) := rotate p y = y

def D := {w : L' | ∀ p : G, fixpunkt w p}



def rotationsAchse (p : GL (Fin 3) Real) : Set r_3 :=
  {w : r_3 | fixpunkt w p}


-- Free group

inductive erzeuger_t
  | gl_a : erzeuger_t
  | gl_b : erzeuger_t
  deriving DecidableEq

abbrev G_list := {w : List (erzeuger_t × Bool) | w = FreeGroup.reduce w}

def item_to_matrix (i : erzeuger_t × Bool) : GL (Fin 3) Real :=
  match i with
  | (erzeuger_t.gl_a, true) => gl_a
  | (erzeuger_t.gl_a, false) => gl_a'
  | (erzeuger_t.gl_b, true) => gl_b
  | (erzeuger_t.gl_b, false) => gl_b'


def list_to_matrix (w : List (erzeuger_t × Bool)) : GL (Fin 3) Real :=
  match w with
  | [] => gl_one
  | (head::rest) =>  list_to_matrix rest * item_to_matrix head

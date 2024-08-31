import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Finset.NAry



variable {X : Type*} (G : Type*)

variable [Group G] [MulAction G X]

open Set

structure Equidecomposition (A B : Set X) extends A ≃ B where
    elements : Finset G
    moves_by : ∀ a : A, ∃ g ∈ elements, toEquiv a = g • (a : X)

notation:50 A " ≃ₑ[" G:50 "] " B:50 => Equidecomposition G A B

def Equidecomposable (A B : Set X) : Prop := Nonempty (A ≃ₑ[G] B)


def Paradoxical (X : Type*) [MulAction G X] : Prop :=
    ∃ A B : Set X, Disjoint A B ∧ Equidecomposable G A univ ∧ Equidecomposable G B univ

instance equidecompositionEquivLike {A B : Set X} : EquivLike (A ≃ₑ[G] B) A B where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' _ _ he _ := by
    rename_i inst inst_1 x x_1 x_2
    simp_all only [DFunLike.coe_fn_eq]
    sorry




example (x : X) (p : X → Prop) : (∃ y ∈ ({x} : Set X), p y) ↔ p x := by exact exists_eq_left

def Equidecomposition.refl (A : Set X) : A ≃ₑ[G] A where
    toEquiv := Equiv.refl A
    elements := {1}
    moves_by := by simp

def Equidecomposition.symm [DecidableEq G] {A B : Set X} (f : A ≃ₑ[G] B): B ≃ₑ[G] A where
  toEquiv := f.toEquiv.symm
  elements := f.elements.image (·)⁻¹
  moves_by := by
    rintro b
    rcases f.moves_by (f.toEquiv.symm b) with ⟨g, g_mem, hg⟩
    use g⁻¹
    simp only [Finset.mem_image, Pi.inv_apply, inv_inj, exists_eq_right]
    refine ⟨g_mem, smul_left_cancel g ?_⟩
    simp[← hg]

def Equidecomposition.trans [DecidableEq G] {A B C : Set X} (f : A ≃ₑ[G] B) (i : B ≃ₑ[G] C)
    : A ≃ₑ[G] C where
  toEquiv := f.toEquiv.trans i.toEquiv
  elements := Finset.image₂ (· * ·) i.elements f.elements
  moves_by := by
    rintro a
    rcases f.moves_by a with ⟨g, g_mem, hg⟩
    rcases i.moves_by (f.toEquiv a) with ⟨k, k_mem, hk⟩
    simp only [Finset.mem_image₂, Equiv.trans_apply, exists_exists_and_exists_and_eq_and]
    use k, k_mem, g, g_mem
    rw [mul_smul, ← hg, ← hk]

import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.FunLike.Basic

import CMSC22500Sylow.GLnFp

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html
-- Basis.mkFinCons

variable {n p : ℕ} [Fact p.Prime]

def myBasis (n p : ℕ) [Fact p.Prime] : Type := Basis (Fin n) (ZMod p) (Fin n -> ZMod p)

def nkM_li_vectors (n k p : ℕ) [Fact p.Prime] : Type := {v : (Fin k -> (Fin n -> ZMod p)) // LinearIndependent (ZMod p) v}

instance (k : ℕ) : Fintype (nkM_li_vectors n k p) := sorry
instance : Fintype (myBasis n p) := sorry
instance (k : ℕ) (v : nkM_li_vectors n k p) : Fintype {x // x ∉ Submodule.span (ZMod p) (Set.range v.1)} := sorry

lemma excluded_submodule_card (k : ℕ) (v : nkM_li_vectors n k p) : Fintype.card {x // x ∉ Submodule.span (ZMod p) (Set.range v.1)} = p^n - p^k :=
  sorry

lemma basis_card (k : ℕ) : Fintype.card (nkM_li_vectors n k p) = Finset.prod (Finset.range k) (λ i ↦ p^n - p^i) := by
  induction k
  case zero =>
    simp
    sorry
  case succ k ih =>
    unfold nkM_li_vectors at *
    rw [Finset.range_succ]
    rw [Finset.prod_insert]
    . rw [<-ih]
      sorry
    . exact Finset.not_mem_range_self

noncomputable def basis_equiv_li_to (n p : ℕ) [Fact p.Prime] : (myBasis n p) -> (nkM_li_vectors n n p) := by
  intros b
  unfold myBasis at *
  exact ⟨⇑b, Basis.linearIndependent b⟩

noncomputable def basis_equiv_li_inv (n p : ℕ) [Fact p.Prime] : (nkM_li_vectors n n p) -> (myBasis n p) := by
  intros v
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range v.1) := sorry
  exact Basis.mk v.2 hsp

lemma left_inv_li : Function.LeftInverse (basis_equiv_li_inv n p) (basis_equiv_li_to n p) := by
  unfold Function.LeftInverse
  unfold basis_equiv_li_inv
  unfold basis_equiv_li_to
  unfold myBasis
  unfold Basis.mk
  simp
  sorry

lemma right_inv_li : Function.RightInverse (basis_equiv_li_inv n p) (basis_equiv_li_to n p) := by
  unfold Function.RightInverse
  unfold Function.LeftInverse
  unfold basis_equiv_li_inv
  unfold basis_equiv_li_to
  simp

noncomputable def basis_equiv_li [Fact p.Prime] : (myBasis n p) ≃ (nkM_li_vectors n n p) := {
  toFun := basis_equiv_li_to n p
  invFun := basis_equiv_li_inv n p
  left_inv := left_inv_li,
  right_inv := right_inv_li,
}

def my_linear_equiv := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n -> ZMod p)

noncomputable def basis_equiv_to (n p : ℕ) [Fact p.Prime] : (myBasis n p) -> (GLₙFₚ n p) :=
  λ b ↦
    (Matrix.GeneralLinearGroup.toLinear.symm) (my_linear_equiv.symm b.equivFun)

noncomputable def basis_equiv_inv (n p : ℕ) [Fact p.Prime] : (GLₙFₚ n p) -> (myBasis n p) :=
  λ M ↦
    Basis.ofEquivFun (my_linear_equiv (Matrix.GeneralLinearGroup.toLinear M))

lemma left_inv  : Function.LeftInverse (basis_equiv_inv n p) (basis_equiv_to n p) := by
  unfold Function.LeftInverse
  unfold basis_equiv_inv
  unfold basis_equiv_to
  simp

lemma right_inv : Function.RightInverse (basis_equiv_inv n p) (basis_equiv_to n p) := by
  unfold Function.RightInverse
  unfold Function.LeftInverse
  unfold basis_equiv_to
  unfold basis_equiv_inv
  simp

noncomputable def basis_equiv [Fact p.Prime] : (myBasis n p) ≃ GLₙFₚ n p:= {
  toFun := basis_equiv_to n p,
  invFun := basis_equiv_inv n p,
  left_inv := left_inv,
  right_inv := right_inv,
}

lemma GLₙFₚ_card : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p ^ n - p ^ i) := by
  rw [←Fintype.card_congr basis_equiv]
  rw [Fintype.card_congr basis_equiv_li]
  exact basis_card n

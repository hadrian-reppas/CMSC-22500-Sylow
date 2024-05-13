import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Basis

import CMSC22500Sylow.GLnFp

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html
-- Basis.mkFinCons

variable {n p : ℕ} [Fact p.Prime]

def nkMBasis (n k p : ℕ) [Fact p.Prime] : Type := Basis (Fin k) (ZMod p) (Fin n -> ZMod p)

instance (k : ℕ) : Fintype (nkMBasis n k p) := sorry

-- TODO: figure out what to do here
-- def my_hli (v : Fin n -> ZMod p) : Prop := ∀(c : ZMod p), (∀ x ∈ (Fin n -> ZMod p)), c • v + x = 0 → c = 0
-- def my_hsp (v : Fin n -> ZMod p) : Prop := ∀(z : Fin n -> ZMod p), ∃ (c : ZMod p), ((z + c • v) ∈ (Fin n -> ZMod p))

-- def independent_column (k : ℕ) (b : nkMBasis n k p) : Type :=
--   {v : Fin n -> ZMod p // (my_hli v /\ my_hsp v)}

lemma basis_card (k : ℕ) : Fintype.card (nkMBasis n k p) = Finset.prod (Finset.range k) (λ i ↦ p^n - p^i) := by
  induction k
  case zero =>
    simp
    sorry
  case succ k ih =>
    unfold nkMBasis at *
    rw [Finset.range_succ]
    rw [Finset.prod_insert]
    . rw [<-ih]
      sorry
    . exact Finset.not_mem_range_self

def my_linear_equiv := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n -> ZMod p)

noncomputable def basis_equiv_to (n p : ℕ) [Fact p.Prime] : (nkMBasis n n p) -> (GLₙFₚ n p) :=
  λ b ↦
    (Matrix.GeneralLinearGroup.toLinear.symm) (my_linear_equiv.symm b.equivFun)

noncomputable def basis_equiv_inv (n p : ℕ) [Fact p.Prime] : (GLₙFₚ n p) -> (nkMBasis n n p) :=
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

noncomputable def basis_equiv [Fact p.Prime] : (nkMBasis n n p) ≃ GLₙFₚ n p:= {
  toFun := basis_equiv_to n p,
  invFun := basis_equiv_inv n p,
  left_inv := left_inv,
  right_inv := right_inv,
}

lemma GLₙFₚ_card : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p ^ n - p ^ i) := by
  rw [←Fintype.card_congr basis_equiv]
  exact basis_card n

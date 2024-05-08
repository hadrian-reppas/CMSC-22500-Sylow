import Mathlib.GroupTheory.Sylow

import CMSC22500Sylow.GLₙFₚ
import CMSC22500Sylow.SubgroupGLₙFₚ
import CMSC22500Sylow.Unitriangularₙₚ

-- I think these are the right sizes
-- We might not need these if we can prove p-Sylowness directly
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html
-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf

lemma GL_card (n p : ℕ) [Fact p.Prime] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p^n - p^i) := sorry

def UT_Sylow (n p : ℕ) [Fact p.Prime] : Sylow p (GLₙFₚ n p) := {
  carrier := UpperTriangularₙₚ n p,
  mul_mem' := (UpperTriangularₙₚ n p).mul_mem',
  one_mem' := (UpperTriangularₙₚ n p).one_mem',
  inv_mem' := (UpperTriangularₙₚ n p).inv_mem',
  isPGroup' := sorry,
  is_maximal' := sorry,
}

-- Claim from Calegari's proof
def subset_Sylow (G : Type u) [Group G] (H : Subgroup G) (Γ : Type v) [Group Γ] (h : Γ ≃* H) (P : Sylow p G) : Sylow p Γ := sorry

-- Sylow I
theorem SylowI (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Fintype G] [DecidableEq G] : Sylow p G :=
  subset_Sylow (GLₙFₚ (Fintype.card G) p) (GLₙFₚ_hom G p).range G (subgroup_GLₙFₚ p G) (UT_Sylow (Fintype.card G) p)

import Mathlib.GroupTheory.Sylow

import CMSC22500Sylow.GLnFp
import CMSC22500Sylow.SubgroupGLnFp
import CMSC22500Sylow.Unitriangular

-- Given `GLₙFₚ_card` and `Unitriangular_card`, we have to prove that `Unitriangularₙₚ`
-- is a `p`-Sylow of `GLₙFₚ`. I think we can use the following proof along with the following
-- lemma from Mathlib to get the multiplicity of `p`.
-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Multiplicity.html#multiplicity.Finset.prod

def UT_Sylow (n p : ℕ) [Fact p.Prime] : Sylow p (GLₙFₚ n p) := {
  carrier := Unitriangularₙₚ n p,
  mul_mem' := (Unitriangularₙₚ n p).mul_mem',
  one_mem' := (Unitriangularₙₚ n p).one_mem',
  inv_mem' := (Unitriangularₙₚ n p).inv_mem',
  isPGroup' := sorry,
  is_maximal' := sorry,
}

-- Calegari's lemma: If `H ⊆ G`, `Γ ≃ H` and `P ⊆ G` is a `p`-Sylow, then we can
-- construct a `p`-Sylow of `Γ`.
lemma Calegari'sLemma (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] (H : Subgroup G)
  (Γ : Type v) [Group Γ] (h : Γ ≃* H) (P : Sylow p G) : Sylow p Γ := sorry

-- Sylow I
theorem SylowI (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Fintype G] [DecidableEq G] : Sylow p G :=
  Calegari'sLemma p (GLₙFₚ (Fintype.card G) p) (GLₙFₚ_hom G p).range G (subgroup_GLₙFₚ p G) (UT_Sylow (Fintype.card G) p)

import Mathlib.GroupTheory.Sylow

import CMSC22500Sylow.GLnFp
import CMSC22500Sylow.GLnFpCard
import CMSC22500Sylow.SubgroupGLnFp
import CMSC22500Sylow.Unitriangular
import CMSC22500Sylow.UnitriangularCard

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Multiplicity.html#multiplicity.Finset.prod
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factorization/Basic.html#Nat.multiplicity_eq_factorization
lemma card_eq {n p : ℕ} [pp : Fact p.Prime] : Fintype.card (Unitriangularₙₚ n p) = p ^ (Fintype.card (GLₙFₚ n p)).factorization p := by
  rw [Unitriangular_card, GLₙFₚ_card]
  have h₁ : (Finset.prod (Finset.range n) fun i ↦ p ^ n - p ^ i) ≠ 0 := sorry
  have h₂ := Nat.multiplicity_eq_factorization pp.out h₁
  have h₃ := multiplicity.multiplicity_pow_self_of_prime (Nat.Prime.prime pp.out) (n * (n - 1) / 2)
  have h₄ : multiplicity p (Finset.prod (Finset.range n) fun i ↦ p ^ n - p ^ i) = multiplicity p (p ^ (n * (n - 1) / 2)) := sorry
  have h₅ := h₂.symm.trans (h₄.trans h₃)
  simp at h₅
  rw [h₅]

def GLₙFₚSylow (n p : ℕ) [Fact p.Prime] : Sylow p (GLₙFₚ n p) := Sylow.ofCard (Unitriangularₙₚ n p) card_eq

-- Calegari's lemma: If `H ⊆ G`, `Γ ≃ H` and `P` is a `p`-Sylow of `G`, then we can
-- construct a `p`-Sylow of `Γ`.
lemma Calegari'sLemma (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] (H : Subgroup G)
  (Γ : Type v) [Group Γ] (h : Γ ≃* H) (P : Sylow p G) : Sylow p Γ := sorry

-- Sylow I
theorem SylowI (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Fintype G] [DecidableEq G] : Sylow p G :=
  Calegari'sLemma p (GLₙFₚ (Fintype.card G) p) (GLₙFₚ_hom G p).range G (subgroup_GLₙFₚ p G) (GLₙFₚSylow (Fintype.card G) p)

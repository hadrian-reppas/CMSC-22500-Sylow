import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Multiplicity

import CMSC22500Sylow.GLnFp
import CMSC22500Sylow.GLnFpCard
import CMSC22500Sylow.SubgroupGLnFp
import CMSC22500Sylow.Unitriangular
import CMSC22500Sylow.UnitriangularCard

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Multiplicity.html#multiplicity.Finset.prod
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factorization/Basic.html#Nat.multiplicity_eq_factorization

lemma multiplicity_0 {p i : ℕ} (hp : p.Prime) (hi : i > 0) : multiplicity p (p ^ i - 1) = 0 := by
  refine multiplicity.multiplicity_eq_zero.mpr ?_
  have h₁ : p ∣ p ^ i := by refine dvd_pow_self p (Nat.not_eq_zero_of_lt hi)
  have h₂ : p > 1 := Nat.Prime.one_lt hp
  admit

lemma diff_multiplicity {n p i : ℕ} (pp : Prime p) (h : i < n) : multiplicity p (p ^ n - p ^ i) = i := by
  have h₁ : p ^ n - p ^ i = p ^ i * (p ^ (n - i) - 1) := by
    induction i
    case zero => simp
    case succ i' _ =>
      simp at *
      rw [
        Nat.mul_sub_left_distrib (p ^ Nat.succ i') (p ^ (n - Nat.succ i')) 1,
        ←Nat.pow_add p (Nat.succ i') (n - Nat.succ i'),
        ←Nat.add_sub_of_le (Nat.le_of_succ_le h),
      ]
      simp
  rw [
    h₁,
    multiplicity.mul pp,
    multiplicity_0 (Prime.nat_prime pp) (Nat.zero_lt_sub_of_lt h),
    multiplicity.multiplicity_pow_self (Prime.ne_zero pp) (Prime.not_unit pp),
  ]
  simp

lemma p_multiplicity {n p : ℕ} [pp : Fact p.Prime] : multiplicity p (Finset.prod (Finset.range n) λ i ↦ p ^ n - p ^ i) = multiplicity p (p ^ (n * (n - 1) / 2)) := by
  rw [multiplicity.Finset.prod (Nat.Prime.prime pp.out) (Finset.range n) (λ i ↦ p ^ n - p ^ i)]
  rw [multiplicity.multiplicity_pow_self (Nat.Prime.ne_zero pp.out) (Prime.not_unit (Nat.Prime.prime pp.out))]
  admit

lemma card_eq {n p : ℕ} [pp : Fact p.Prime] : Fintype.card (Unitriangularₙₚ n p) = p ^ (Fintype.card (GLₙFₚ n p)).factorization p := by
  rw [Unitriangular_card, GLₙFₚ_card]
  have h₁ : (Finset.prod (Finset.range n) fun i ↦ p ^ n - p ^ i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Nat.sub_ne_zero_iff_lt.mpr
    exact (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt pp.out)).mpr (List.mem_range.mp hi)
  have h₂ := Nat.multiplicity_eq_factorization pp.out h₁
  have h₃ := multiplicity.multiplicity_pow_self_of_prime (Nat.Prime.prime pp.out) (n * (n - 1) / 2)
  have h₄ := h₂.symm.trans (p_multiplicity.trans h₃)
  simp at h₄
  rw [h₄]

def GLₙFₚSylow (n p : ℕ) [Fact p.Prime] : Sylow p (GLₙFₚ n p) := Sylow.ofCard (Unitriangularₙₚ n p) card_eq

-- Calegari's lemma: If `H ⊆ G`, `Γ ≃ H` and `P` is a `p`-Sylow of `G`, then we can
-- construct a `p`-Sylow of `Γ`.
lemma Calegari'sLemma (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] (H : Subgroup G)
  (Γ : Type v) [Group Γ] (h : Γ ≃* H) (P : Sylow p G) : Sylow p Γ := sorry

-- Sylow I
theorem SylowI (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Fintype G] [DecidableEq G] : Sylow p G :=
  Calegari'sLemma p (GLₙFₚ (Fintype.card G) p) (GLₙFₚ_hom G p).range G (subgroup_GLₙFₚ p G) (GLₙFₚSylow (Fintype.card G) p)

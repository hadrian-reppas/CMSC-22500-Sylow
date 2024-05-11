import CMSC22500Sylow.GLnFpCard
import CMSC22500Sylow.UnitriangularCard

lemma multiplicity_0 {p i : ℕ} (hp : p.Prime) (hi : i > 0) : multiplicity p (p ^ i - 1) = 0 := by
  refine multiplicity.multiplicity_eq_zero.mpr ?_
  have h₁ : p ∣ p ^ i := by refine dvd_pow_self p (Nat.not_eq_zero_of_lt hi)
  have h₂ : p > 1 := Nat.Prime.one_lt hp
  intro h
  have h₄ : p ∣ p ^ i - (p ^ i - 1) := Nat.dvd_sub' h₁ h
  have h₅ : p ^ i - (p ^ i - 1) = 1 := by
    refine Nat.sub_sub_self ?h
    exact Nat.one_le_pow i p (Nat.zero_lt_of_lt h₂)
  rw [h₅] at h₄
  exact hp.not_unit (isUnit_of_dvd_one h₄)

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

lemma triangle {n : ℕ} : (Finset.sum (Finset.range n) fun x ↦ (x : PartENat)) = ↑(n * (n - 1) / 2) := by
  induction n
  case zero => rfl
  case succ k ih =>
    simp
    rw [Finset.sum_range_succ_comm, ih]
    rw [←Nat.cast_add]
    apply congrArg Nat.cast
    nth_rewrite 1 [←Nat.mul_div_cancel k Nat.zero_lt_two]
    have h₂ : k * 2 / 2 + k * (k - 1) / 2 = (k * 2 + k * (k - 1)) / 2 := by
      rw [←Nat.add_div_of_dvd_left]
      exact Even.two_dvd (Nat.even_mul_pred_self k)
    rw [h₂]
    cases k
    case zero => rfl
    case succ k' =>
      apply Mathlib.Tactic.LinearCombination.pf_div_c
      rw [←Nat.left_distrib]
      nth_rewrite 2 [Nat.mul_comm]
      simp
      rw [Nat.add_comm]

lemma p_multiplicity {n p : ℕ} [pp : Fact p.Prime] : multiplicity p (Finset.prod (Finset.range n) λ i ↦ p ^ n - p ^ i) = multiplicity p (p ^ (n * (n - 1) / 2)) := by
  rw [multiplicity.Finset.prod (Nat.Prime.prime pp.out) (Finset.range n) (λ i ↦ p ^ n - p ^ i)]
  rw [multiplicity.multiplicity_pow_self (Nat.Prime.ne_zero pp.out) (Prime.not_unit (Nat.Prime.prime pp.out))]
  have h₁ : ∀ i ∈ Finset.range n, multiplicity p (p ^ n - p ^ i) = i := by
    intro i h
    have h₁ : i < n := List.mem_range.mp h
    exact diff_multiplicity (Nat.Prime.prime pp.out) h₁
  rw [Finset.sum_congr rfl h₁]
  exact triangle

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

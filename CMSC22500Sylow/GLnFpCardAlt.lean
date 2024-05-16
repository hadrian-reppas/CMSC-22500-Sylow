import Mathlib.Data.Matrix.Rank

import CMSC22500Sylow.GLnFp

instance [Fact p.Prime] : Fintype (GLₙFₚ n p) := instFintypeUnits

def MaxRank {n p k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod p)) := M.rank = k
def Independent (n p k : ℕ) := { M : Matrix (Fin k) (Fin n) (ZMod p) // MaxRank M }

instance fintype_vecs {n p k : ℕ} [Fact p.Prime] : Fintype (Fin k -> Fin n -> ZMod p) := Pi.fintype
noncomputable instance MaxRankDec {n p k : ℕ} [Fact p.Prime] : DecidablePred (@MaxRank n p k) := Classical.decPred (@MaxRank n p k)
noncomputable instance {n p k : ℕ} [Fact p.Prime] : Fintype (Independent n p k) := by
  unfold Independent
  exact @Subtype.fintype (Fin k -> Fin n -> ZMod p) (@MaxRank n p k) MaxRankDec fintype_vecs

def NotInRange {n p k : ℕ} [Fact p.Prime] (M : Independent n p k) := { v // v ∉ LinearMap.range M.val.vecMulLinear }

-- Adding a row that is linearly independent of existing rows gives a max rank matrix
lemma li_cons_max_rank {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k) (v : NotInRange M) : MaxRank (Matrix.vecCons v.val M.val) := sorry

-- Given a matrix `M` and a vector `v` not in `M`'s range, this function adds `v` as a row to `M`
def cons {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k) (v : NotInRange M) : Independent n p k.succ := {
  val := Matrix.vecCons v.val M.val,
  property := li_cons_max_rank h M v,
}

-- If we remove the first row from a matrix with max rank, we get a matrix with max rank
lemma max_rank_tail {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k.succ) : MaxRank (Matrix.vecTail M.val) := sorry

-- This removes the first row of `M`
def tail {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k.succ) : Independent n p k := {
  val := Matrix.vecTail M.val,
  property := max_rank_tail h M,
}

-- The first row of a matrix with max rank is linearly independent of subsequent rows
lemma head_not_in_range {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k.succ) : Matrix.vecHead M.val ∉ LinearMap.range (Matrix.vecMulLinear (tail h M).val) := sorry

-- This returns the first row of `M`, which will not be in the range of `tail M`
def head {n p k : ℕ} [Fact p.Prime] (h : k < n) (M : Independent n p k.succ) : NotInRange (tail h M) := {
  val := Matrix.vecHead M.val,
  property := head_not_in_range h M,
}

def equiv_sigma_fun (n p k : ℕ) [pp : Fact p.Prime] (h : k < n) (M : Independent n p k.succ) : Sigma (@NotInRange n p k pp) := ⟨tail h M, head h M⟩
def equiv_sigma_inv (n p k : ℕ) [pp : Fact p.Prime] (h : k < n) (q : Sigma (@NotInRange n p k pp)) : Independent n p k.succ := cons h q.fst q.snd

lemma equiv_sigma (n p k : ℕ) [pp : Fact p.Prime] (h : k < n) : Independent n p k.succ ≃ Sigma (@NotInRange n p k pp) := {
  toFun := equiv_sigma_fun n p k h,
  invFun := equiv_sigma_inv n p k h,
  left_inv := by
    intro x
    unfold equiv_sigma_fun
    unfold equiv_sigma_inv
    unfold cons
    unfold tail
    unfold head
    simp,
  right_inv := by intros x; exact rfl,
}

noncomputable instance {n p k : ℕ} [Fact p.Prime] {M : Independent n p k} : Fintype (NotInRange M) := by
  unfold NotInRange
  exact Fintype.ofFinite { v // v ∉ LinearMap.range (Matrix.vecMulLinear M.val) }

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional.html#LinearMap.finrank_range_add_finrank_ker
lemma range_card {n p k : ℕ} [Fact p.Prime] (M : Independent n p k) : Fintype.card (NotInRange M) = p ^ n - p ^ k := sorry

lemma blah (n p k : ℕ) [pp : Fact p.Prime] : Fintype.card (Independent n p k.succ) = Fintype.card (Independent n p k) * (p ^ n - p ^ k) := by
  by_cases h : n > k
  · have h₁ := Fintype.ofEquiv (Independent n p (Nat.succ k)) (equiv_sigma n p k h)
    have h₂ : Fintype.card (Sigma (@NotInRange n p k pp)) = Finset.univ.sum λ (M : Independent n p k) ↦ Fintype.card (NotInRange M) := by
      have h₃ := @Fintype.card_sigma (Independent n p k) (@NotInRange n p k pp) instFintypeIndependent λ i ↦ instFintypeNotInRange
      rw [←h₃]
      exact @Fintype.card_congr' (Sigma (@NotInRange n p k pp)) (Sigma (@NotInRange n p k pp)) h₁ Sigma.instFintype rfl
    rw [Finset.sum_const_nat (λ M _ ↦ range_card M), Finset.card_univ] at h₂
    rw [←Fintype.ofEquiv_card (equiv_sigma n p k h), ←h₂]
    exact @Fintype.card_congr' (Sigma (@NotInRange n p k pp)) (Sigma (@NotInRange n p k pp)) (Fintype.ofEquiv (Independent n p (Nat.succ k)) (equiv_sigma n p k h)) h₁ rfl
  · have h₁ : n ≤ k := Nat.le_of_not_lt h
    have h₂ : p ^ n - p ^ k = 0 := by
      refine Nat.sub_eq_zero_of_le ?h
      refine Nat.pow_le_pow_of_le_right ?h.hx h₁
      exact Fin.size_pos'
    rw [h₂]
    simp
    have h₃ : IsEmpty (Independent n p (Nat.succ k)) := ⟨by
      intro ⟨M, h⟩
      unfold MaxRank at h
      have h₂ := Matrix.rank_le_width M
      linarith⟩
    exact Fintype.card_eq_zero

lemma Independent_card (n p k : ℕ) [Fact p.Prime] : Fintype.card (Independent n p k) = Finset.prod (Finset.range k) (λ i ↦ p ^ n - p ^ i) := by
  induction k
  case zero =>
    simp
    unfold Independent
    refine (Nat.le_antisymm ?h₁ ?h₂).symm
    · refine Nat.one_le_iff_ne_zero.mpr ?h₁.a
      have : Nonempty { M : Matrix (Fin 0) (Fin n) (ZMod p) // MaxRank M } := ⟨{
        val := λ _ _ ↦ 1,
        property := by
          unfold MaxRank
          unfold Matrix.rank
          exact FiniteDimensional.finrank_zero_of_subsingleton,
      }⟩
      apply Fintype.card_ne_zero
    · apply Fintype.card_subtype_le
  case succ k' ih =>
    rw [Finset.prod_range_succ, ←ih]
    exact blah n p k'

lemma max_rank_iff_invertible {n p : ℕ} [Fact p.Prime] (M : Matrix (Fin n) (Fin n) (ZMod p)) : MaxRank M ↔ IsUnit M := by
  apply Iff.intro <;> intro h
  · admit
  · unfold MaxRank
    rw [Matrix.rank_of_isUnit M h]
    exact Fintype.card_fin n

lemma foo (n p : ℕ) [Fact p.Prime] : GLₙFₚ n p ≃ Independent n p n := {
  toFun := λ M ↦ {
    val := M.val,
    property := (max_rank_iff_invertible M.val).mpr (Units.isUnit M),
  },
  invFun := λ M ↦ IsUnit.unit ((max_rank_iff_invertible M.val).mp M.property),
  left_inv := by unfold Function.LeftInverse; simp,
  right_inv := by unfold Function.RightInverse; unfold Function.LeftInverse; simp,
}

theorem GLₙFₚ_card [Fact p.Prime] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p ^ n - p ^ i) := by
  rw [Fintype.card_congr (foo n p)]
  exact Independent_card n p n

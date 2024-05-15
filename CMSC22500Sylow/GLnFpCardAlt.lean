import CMSC22500Sylow.GLnFp

instance [Fact p.Prime] : Fintype (GLₙFₚ n p) := instFintypeUnits

def Independent (n p k : ℕ) := { vs : Fin k -> Fin n -> ZMod p // LinearIndependent (ZMod p) vs }

instance fintype_vecs {n p k : ℕ} [Fact p.Prime] : Fintype (Fin k -> Fin n -> ZMod p) := Pi.fintype
noncomputable instance LinearIndependentDec {n p k : ℕ} [Fact p.Prime] : DecidablePred (λ (vs : Fin k -> Fin n -> ZMod p) ↦ LinearIndependent (ZMod p) vs) :=
  Classical.decPred fun vs ↦ LinearIndependent (ZMod p) vs
noncomputable instance {n p k : ℕ} [Fact p.Prime] : Fintype (Independent n p k) := by
  unfold Independent
  exact @Subtype.fintype (Fin k -> Fin n -> ZMod p) (λ vs ↦ LinearIndependent (ZMod p) vs) LinearIndependentDec fintype_vecs

lemma blah (n p k : ℕ) [Fact p.Prime] : Fintype.card (Independent n p (Nat.succ k)) = Fintype.card (Independent n p k) * (p ^ n - p ^ k) := by
  apply?

lemma Independent_card (n p k : ℕ) [Fact p.Prime] : Fintype.card (Independent n p k) = Finset.prod (Finset.range k) (λ i ↦ p ^ n - p ^ i) := by
  induction k
  case zero =>
    simp
    unfold Independent
    refine (Nat.le_antisymm ?h₁ ?h₂).symm
    · refine Nat.one_le_iff_ne_zero.mpr ?h₁.a
      have : Nonempty { vs : Fin 0 -> Fin n -> ZMod p // LinearIndependent (ZMod p) vs } := ⟨{
        val := λ _ _ ↦ 1,
        property := linearIndependent_empty_type,
      }⟩
      apply Fintype.card_ne_zero
    · apply Fintype.card_subtype_le
  case succ k' ih =>
    rw [Finset.prod_range_succ, ←ih]
    exact blah n p k'

lemma foo (n p : ℕ) [Fact p.Prime] : GLₙFₚ n p ≃ Independent n p n := sorry

theorem GLₙFₚ_card [Fact p.Prime] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p ^ n - p ^ i) := by
  rw [Fintype.card_congr (foo n p)]
  exact Independent_card n p n

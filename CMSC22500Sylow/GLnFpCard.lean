import CMSC22500Sylow.GLnFp
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Basic

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html

variable {n p : ℕ} [Fact p.Prime]

-- TODO: variable ordering for this is kinda digusting
def FullRank (k : ℕ) (M : (Matrix (Fin n) (Fin k) (ZMod p))) : Prop := Matrix.rank M = k
noncomputable instance (k : ℕ) : DecidablePred (@FullRank n p k) := Classical.decPred (FullRank k)

def FullRankₙₖₚ (k : ℕ) : Type := {x : (Matrix (Fin n) (Fin k) (ZMod p)) // FullRank k x}

--Matrix.instFintypeOfDecidableEq
instance (k : ℕ) : Fintype (Matrix (Fin n) (Fin k) (ZMod p)) := sorry
noncomputable instance : Fintype (@FullRankₙₖₚ n p k) := Subtype.fintype (FullRank k)

lemma nkM_card (k : ℕ) [Fact p.Prime] : Fintype.card (@FullRankₙₖₚ n p k) = Finset.prod (Finset.range k) (λ i ↦ p^n - p^i) := by
  induction k
  case zero =>
    simp
    sorry
  case succ k ih =>
    sorry

def nkM_equiv_to : (@FullRankₙₖₚ n p n) -> (GLₙFₚ n p) := sorry

def nkM_equiv_inv : (GLₙFₚ n p) -> (@FullRankₙₖₚ n p n) := by
  intros M
  have M_rank : Matrix.rank M.val = n := sorry
  exact ⟨M.val, M_rank⟩

lemma left_inv : Function.LeftInverse (@nkM_equiv_inv n p) (@nkM_equiv_to n p) := sorry

lemma right_inv : Function.RightInverse (@nkM_equiv_inv n p) (@nkM_equiv_to n p) := sorry

def nkM_equiv : @FullRankₙₖₚ n p n ≃ GLₙFₚ n p:= {
  toFun := nkM_equiv_to
  invFun := nkM_equiv_inv,
  left_inv := left_inv,
  right_inv := right_inv,
}

lemma GLₙFₚ_card : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p^n - p^i) := by
  rw [←Fintype.card_congr nkM_equiv]
  exact nkM_card n

import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Init.Order.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

abbrev GLₙFₚ (n p : ℕ) := GL (Fin n) (ZMod p)

variable {n p : ℕ} {M N : GLₙFₚ n p}

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup : Group (GLₙFₚ n p) := Units.instGroup

def ZerosUnderDiag (M : GLₙFₚ n p) : Prop := ∀ i j, j < i → M.val i j = 0
def OnesOnDiag (M : GLₙFₚ n p) : Prop := ∀ i, M.val i i = 1

-- A predicate for upper triangular matrices
def IsUpperTriangular (M : GLₙFₚ n p) : Prop := ZerosUnderDiag M ∧ OnesOnDiag M

-- The product of two UT matrices has zeros under the diagonal
lemma UT_mul_zeros (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) (i j : Fin n) (h : j < i)
   : Matrix.dotProduct (λ k ↦ M.val i k) (λ k ↦ N.val k j) = 0 :=
  Finset.sum_eq_zero (λ k _ ↦
    if hki : k < i then by simp [hM.left i k hki]
    else by simp [hN.left k j (lt_of_lt_of_le h (not_lt.mp hki))])

lemma ne_lt_or_ge {a b : Fin n} (h : a ≠ b) : a < b ∨ a > b :=
  match le_or_gt a b with
  | .inl h₁ => match lt_or_eq_of_le h₁ with
    | .inl h₂ => .inl h₂
    | .inr h₂ => absurd h₂ h
  | .inr h₁ => .inr h₁

lemma ZUD_prod_0 {i j : Fin n} (hM : ZerosUnderDiag M) (hN : ZerosUnderDiag N) (h : j ≠ i)
   : (M.val i j) * (N.val j i) = 0 :=
    match ne_lt_or_ge h with
    | .inl h => by simp [hM i j h]
    | .inr h => by simp [hN j i h]

-- The product of two UT matrices has ones on the diagonal
lemma UT_mul_ones (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) (i : Fin n)
   : Matrix.dotProduct (λ k ↦ M.val i k) (λ k ↦ N.val k i) = 1 := by simp [
      Matrix.dotProduct,
      Finset.sum_eq_single_of_mem i
        (Finset.mem_univ i)
        (λ _ _ h ↦ ZUD_prod_0 hM.left hN.left h),
      hM.right i, hN.right i
    ]

instance : Invertible M.val := Units.invertible M

lemma ZUD_block_triangular (hM : ZerosUnderDiag M) : Matrix.BlockTriangular M.val id := hM

-- The inverse of an ZUD matrix is a ZUD matrix
lemma ZUD_inv_ZUD (h₁ : ZerosUnderDiag M) : ZerosUnderDiag M⁻¹ :=
  λ i j h₂ ↦ by
    simp [Matrix.coe_units_inv M]
    exact (Matrix.blockTriangular_inv_of_blockTriangular (ZUD_block_triangular h₁) h₂)

-- The inverse of an UT matrix has ones on the diagonal
lemma UT_inv_ones {i : Fin n} (h : IsUpperTriangular M) : M.inv i i = 1 :=
  have h₁ : (M.inv * M) i i = 1 := by simp [M.inv_val, Matrix.one_apply_eq i]
  have h₂ : Matrix.dotProduct (λ k ↦ M.inv i k) (λ k ↦ M k i) = 1 := h₁
  have h₃ : Matrix.dotProduct (λ k ↦ M.inv i k) (λ k ↦ M k i) = M.inv i i * M i i :=
    Finset.sum_eq_single_of_mem i
      (Finset.mem_univ i)
      (λ j _ h₁ ↦ by
        have h' := ZUD_prod_0 (ZUD_inv_ZUD h.left) h.left h₁
        simp at *
        exact h')
  have h₄ := h₃.symm.trans h₂
  have h₅ : M.val i i = 1 := h.right i
  have h₆ : M.inv i i = 1 := by
    rw [h₅] at h₄
    simp at *
    exact h₄
  h₆

-- The subgroup of upper triangular matrices
def UpperTriangularₙₚ (n p : ℕ) : Subgroup (GLₙFₚ n p) := {
  carrier := IsUpperTriangular,
  mul_mem' := λ ha hb ↦ ⟨UT_mul_zeros ha hb, UT_mul_ones ha hb⟩,
  one_mem' := ⟨
    λ _ _ h ↦ Matrix.one_apply_ne (Ne.symm (Fin.ne_of_lt h)),
    Matrix.one_apply_eq
  ⟩,
  inv_mem' := λ h ↦ ⟨ZUD_inv_ZUD h.left, λ _ ↦ UT_inv_ones h⟩
}

instance [h : Fact (Prime p)] : NeZero p := ⟨Prime.ne_zero h.out⟩
instance [Fact (Prime p)] : Fintype (GLₙFₚ n p) := instFintypeUnits
noncomputable instance [Fact (Prime p)] : Fintype (UpperTriangularₙₚ n p) := Fintype.ofFinite (UpperTriangularₙₚ n p)


-- I think these are the right sizes
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
lemma UT_card [Fact (Prime p)] : Fintype.card (UpperTriangularₙₚ n p) = p ^ (n * (n - 1) / 2) := sorry
lemma GL_card [Fact (Prime p)] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p^n - p^i) := sorry

-- The injection from a permutation `σ : Equiv.Perm G` to a permutation matrix
def perm_to_matrix {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
  (σ : Equiv.Perm G) : Matrix G G (ZMod p) := λ i j ↦ if σ i = j then 1 else 0

-- A proof that `perm_to_matrix` is a homomorphism
def perm_to_matrix_hom {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
   : MulHom (Equiv.Perm G) (Matrix G G (ZMod p)) := {
  toFun := perm_to_matrix,
  map_mul' := sorry,
}

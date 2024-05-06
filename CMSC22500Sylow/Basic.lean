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
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html
lemma UT_card [Fact (Prime p)] : Fintype.card (UpperTriangularₙₚ n p) = p ^ (n * (n - 1) / 2) := sorry
lemma GL_card [Fact (Prime p)] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p^n - p^i) := sorry

-- The injection from a permutation `σ : Equiv.Perm G` to a permutation matrix
def perm_mat {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
  (σ : Equiv.Perm G) : Matrix G G (ZMod p) := λ i j ↦ if σ j = i then 1 else 0

lemma mul_matrix_apply [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)] (σ : Equiv.Perm G) (M : Matrix G G (ZMod p))
   : (perm_mat σ * M :) i j = M (σ⁻¹ i) j := by
    dsimp [perm_mat, Matrix.mul_apply]
    rw [Finset.sum_eq_single (σ⁻¹ i)]
    · simp
    · intros b _ h
      have h₁ : σ b ≠ i := λ h₁ ↦ by
        have h₂ : b = σ⁻¹ i := Equiv.Perm.eq_inv_iff_eq.mpr h₁
        exact (h h₂).elim
      simp
      intro h₂
      exact (h₁ h₂).elim
    · intro h
      exact (h (Finset.mem_univ (σ⁻¹ i))).elim

-- The map `perm_mat` preserves multiplication
lemma perm_mat_hom_proof [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)] (σ τ : Equiv.Perm G)
   : perm_mat (σ * τ) = (perm_mat σ : Matrix G G (ZMod p)) * (perm_mat τ) := by
    ext i j
    rw [mul_matrix_apply]
    dsimp [perm_mat]
    have h : σ (τ j) = i ↔ τ j = σ⁻¹ i := by
      apply Iff.intro
      · intro h
        exact Equiv.Perm.eq_inv_iff_eq.mpr h
      · intro h
        exact (Equiv.apply_eq_iff_eq_symm_apply σ).mpr h
    refine ite_congr (propext h) (congrFun rfl) (congrFun rfl)

-- The identity permutation maps to the identity matrix
lemma perm_mat_1 [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)] : perm_mat 1 = (1 : Matrix G G (ZMod p)) := by
  ext i j
  unfold perm_mat
  by_cases h : j = i
  · simp [h]
  · simp
    symm
    have h : (1 : Matrix G G (ZMod p)) i j = (1 : Matrix G G (ZMod p)) j i := by
      by_cases h₁ : i = j
      · exact (h h₁.symm).elim
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h₁]
    rw [h]
    exact Matrix.one_apply

-- `perm_mat` is a homomorphism
def perm_mat_hom {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
   : MonoidHom (Equiv.Perm G) (Matrix G G (ZMod p)) := {
  toFun := perm_mat,
  map_one' := perm_mat_1,
  map_mul' := perm_mat_hom_proof,
}

-- The determinant of a permutation matrix is nonzero
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html#Matrix.det_permutation
lemma perm_mat_det {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
  (σ : Equiv.Perm G) : (perm_mat σ).det ≠ (0 : ZMod p) := sorry

-- Permutation matrices are invertible
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.invertibleOfIsUnitDet
instance perm_mat_inv {G : Type u} [Group G] [h₁ : Fintype G] [h₂ : DecidableEq G] [Fact (Prime p)]
  (σ : Equiv.Perm G) : Invertible (perm_mat σ : Matrix G G (ZMod p)) := sorry


/-
-------------------------------------------
-- Everything below here is kind of iffy --
-------------------------------------------
-/


-- If `G` has cardinality `n`, then we have a bijection between `G` and `Fin n`
noncomputable def enumerate (G : Type u) [Fintype G] : G ≃ Fin (Fintype.card G) :=
  have h₁ := Fintype.card_fin (Fintype.card G)
  Classical.choice (Fintype.card_eq.mp h₁.symm)

-- Turn a matrix indexed by `G` into a matrix indexed by `Fin (Fintype.card G)`
noncomputable def reindex {G : Type u} [Fintype G] (M : Matrix G G (ZMod p))
   : Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) (ZMod p) :=
  Matrix.reindex (enumerate G) (enumerate G) M

-- `reindex` is a homomorphism
noncomputable def reindex_hom {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
   : MonoidHom (Matrix G G (ZMod p)) (Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) (ZMod p)) := {
  toFun := reindex,
  map_one' := sorry,
  map_mul' := sorry,
}

-- Reindexed permutation matrices are invertible
instance perm_mat_inv' {G : Type u} [Fintype G] [Group G] [DecidableEq G] [Fact (Prime p)] (σ : Equiv.Perm G)
   : Invertible (reindex (perm_mat σ : Matrix  G G (ZMod p))) := sorry

-- The injection from a permutation `σ : Equiv.Perm G` to a `Fin n`-indexed permutation matrix
noncomputable def perm_mat' {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Fact (Prime p)]
  (σ : Equiv.Perm G) : GLₙFₚ (Fintype.card G) p := {
    val := reindex (perm_mat σ),
    inv := (reindex (perm_mat σ))⁻¹,
    val_inv := Matrix.mul_inv_of_invertible (reindex (perm_mat σ)),
    inv_val := Matrix.inv_mul_of_invertible (reindex (perm_mat σ)),
  }

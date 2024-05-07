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
lemma ZUD_inv_ZUD (h₁ : ZerosUnderDiag M) : ZerosUnderDiag M⁻¹ := λ i j h₂ ↦ by
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

universe u
variable {G : Type u} [hg : Group G] [hft : Fintype G] [hdeq : DecidableEq G]

-- The injection from a permutation `σ : Equiv.Perm G` to a permutation matrix
def perm_mat₀ [Fact p.Prime] (σ : Equiv.Perm G) : Matrix G G (ZMod p) := λ i j ↦ if σ j = i then 1 else 0

lemma mul_matrix_apply [Fact p.Prime] (σ : Equiv.Perm G) (M : Matrix G G (ZMod p)) : (perm_mat₀ σ * M :) i j = M (σ⁻¹ i) j := by
  dsimp [perm_mat₀, Matrix.mul_apply]
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
lemma perm_mat_hom_proof [Fact p.Prime] (σ τ : Equiv.Perm G) : perm_mat₀ (σ * τ) = (perm_mat₀ σ : Matrix G G (ZMod p)) * (perm_mat₀ τ) := by
  ext i j
  rw [mul_matrix_apply]
  dsimp [perm_mat₀]
  have h : σ (τ j) = i ↔ τ j = σ⁻¹ i := by
    apply Iff.intro
    · intro h
      exact Equiv.Perm.eq_inv_iff_eq.mpr h
    · intro h
      exact (Equiv.apply_eq_iff_eq_symm_apply σ).mpr h
  refine ite_congr (propext h) (congrFun rfl) (congrFun rfl)

-- The identity permutation maps to the identity matrix
lemma perm_mat_1 [Fact p.Prime] : perm_mat₀ 1 = (1 : Matrix G G (ZMod p)) := by
  ext i j
  unfold perm_mat₀
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

-- `perm_mat₀` is a homomorphism
def perm_mat₀_hom [Fact p.Prime] : MonoidHom (Equiv.Perm G) (Matrix G G (ZMod p)) := {
  toFun := perm_mat₀,
  map_one' := perm_mat_1,
  map_mul' := perm_mat_hom_proof,
}

lemma perm_mat₀_cols [Fact p.Prime] (σ : Equiv.Perm G) : (1 : Matrix G G (ZMod p)).submatrix id σ = perm_mat₀ σ := by
  ext i j
  unfold Matrix.submatrix
  unfold perm_mat₀
  by_cases h : σ j = i <;> simp [h]
  exact Matrix.one_apply_ne' h

-- The determinant of a permutation matrix is nonzero
lemma perm_mat₀_det [hp : Fact p.Prime] (σ : Equiv.Perm G) : (perm_mat₀ σ).det ≠ (0 : ZMod p) := by
  have h₁ : Matrix.det (1 : Matrix G G (ZMod p)) = 1 := Matrix.det_one
  have h₂ := Matrix.det_permute' σ (1 : Matrix G G (ZMod p))
  simp [h₁] at h₂
  have h₃ : (1 : Matrix G G (ZMod p)).submatrix id σ = perm_mat₀ σ := perm_mat₀_cols σ
  rw [h₃] at h₂
  intro hf
  rw [hf] at h₂
  exact (Int.units_eq_one_or (Equiv.Perm.sign σ)).elim
    (λ h ↦ by rw [h] at h₂; simp at h₂)
    (λ h ↦ by rw [h] at h₂; simp at h₂)

-- Permutation matrices are invertible
noncomputable instance perm_mat₀_inv [hp : Fact p.Prime] (σ : Equiv.Perm G) : Invertible (perm_mat₀ σ : Matrix G G (ZMod p)) := by
  apply Matrix.invertibleOfIsUnitDet
  exact Ne.isUnit (perm_mat₀_det σ)

-- If `G` has cardinality `n`, then we have a bijection between `G` and `Fin n`
noncomputable def enumerate (G : Type u) [Fintype G] : G ≃ Fin (Fintype.card G) :=
  have h₁ := Fintype.card_fin (Fintype.card G)
  Classical.choice (Fintype.card_eq.mp h₁.symm)

-- A square matrix indexed by `Fin (Fintype.card G)`
abbrev FinMat (G : Type u) (α : Type v) [Fintype G] := Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) α

-- Turn a matrix indexed by `G` into a matrix indexed by `Fin (Fintype.card G)`
noncomputable def reindex (M : Matrix G G (ZMod p)) : FinMat G (ZMod p) :=
  Matrix.reindex (enumerate G) (enumerate G) M

lemma reindex_1 [Fact p.Prime] : reindex (1 : Matrix G G (ZMod p)) = 1 := by
  ext i j
  rw [reindex, Matrix.reindex]
  simp
  have : (enumerate G).symm i = (enumerate G).symm j ↔ i = j := ⟨
    λ h ↦
      let f := (enumerate G).symm
      have h₁ : (enumerate G).symm = f := rfl
      by
        rw [h₁] at h
        have : f.invFun (f i) = f.invFun (f j) := congrArg f.invFun h
        simp at *
        exact h,
    λ h ↦ by simp [h],
  ⟩
  rw [Matrix.one_apply]
  by_cases h₂ : i = j <;> simp [h₂]

lemma reindex_mul [Fact p.Prime] (M N : Matrix G G (ZMod p)) : reindex (M * N) = reindex M * reindex N := by
  ext i₀ j₀
  rw [Matrix.mul_apply, reindex, Matrix.reindex]
  simp
  let f := (enumerate G).symm
  have hf : (enumerate G).symm = f := rfl
  rw [hf, Matrix.mul_apply, reindex, Matrix.reindex]
  simp
  rw [hf]
  rw [reindex, Matrix.reindex]
  simp
  rw [hf]
  exact (Equiv.sum_comp f (λ j ↦ M (f i₀) j * N j (f j₀))).symm

-- `reindex` is a homomorphism
noncomputable def reindex_hom [Fact p.Prime] : MonoidHom (Matrix G G (ZMod p)) (FinMat G (ZMod p)) := {
  toFun := reindex,
  map_one' := reindex_1,
  map_mul' := reindex_mul,
}

-- We can compose the two homomorphisms
noncomputable def perm_mat_reindexed [Fact p.Prime] : MonoidHom (Equiv.Perm G) (FinMat G (ZMod p)) :=
  MonoidHom.comp reindex_hom perm_mat₀_hom

-- Reindexed permutation matrices are invertible
noncomputable instance perm_mat_inv' [Fact p.Prime] (σ : Equiv.Perm G) : Invertible (perm_mat_reindexed σ : FinMat G (ZMod p)) := {
  invOf := perm_mat_reindexed σ⁻¹,
  invOf_mul_self := MonoidHom.toHomUnits.proof_2 (perm_mat_reindexed : MonoidHom (Equiv.Perm G) (FinMat G (ZMod p))) σ,
  mul_invOf_self := MonoidHom.toHomUnits.proof_1 (perm_mat_reindexed : MonoidHom (Equiv.Perm G) (FinMat G (ZMod p))) σ,
}

-- The function from a `σ : Equiv.Perm G` to a `Fin n`-indexed permutation matrix
noncomputable def perm_mat_fun [Fact p.Prime] (σ : Equiv.Perm G) : GLₙFₚ (Fintype.card G) p := {
  val := perm_mat_reindexed σ,
  inv := (perm_mat_reindexed σ)⁻¹,
  val_inv := Matrix.mul_inv_of_invertible (perm_mat_reindexed σ),
  inv_val := Matrix.inv_mul_of_invertible (perm_mat_reindexed σ),
}

-- The homomorphism from `Equiv.Perm G` to `GLₙFₚ (Fintype.card G) p`
noncomputable def perm_mat [Fact p.Prime] : MonoidHom (Equiv.Perm G) (GLₙFₚ (Fintype.card G) p) := {
  toFun := perm_mat_fun,
  map_one' := by
    apply Units.liftRight.proof_1 perm_mat_reindexed perm_mat_fun
    intro x
    rfl
  map_mul' := λ x y ↦ by
    apply Units.liftRight.proof_2 perm_mat_reindexed perm_mat_fun (congrFun ?_) x y
    ext x
    rfl
}

-- Next, we prove that `perm_mat` has trivial kernel, so it's injective
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Basic.html#AddMonoidHom.ker_eq_bot_iff
-- Thus, `Equiv.Perm G` is isomorphic to a subgroup of `GLₙFₚ (Fintype.card G) p`


instance [h : Fact p.Prime] : NeZero p := ⟨Nat.Prime.ne_zero h.out⟩
instance [Fact p.Prime] : Fintype (GLₙFₚ n p) := instFintypeUnits
noncomputable instance [Fact p.Prime] : Fintype (UpperTriangularₙₚ n p) := Fintype.ofFinite (UpperTriangularₙₚ n p)

-- I think these are the right sizes
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html
lemma UT_card [Fact p.Prime] : Fintype.card (UpperTriangularₙₚ n p) = p ^ (n * (n - 1) / 2) := sorry
lemma GL_card [Fact p.Prime] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p^n - p^i) := sorry

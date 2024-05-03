import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Init.Order.Defs
import Mathlib.LinearAlgebra.Matrix.Block

abbrev GLₙFₚ (n p : ℕ) := GL (Fin n) (ZMod p)

variable {n p : ℕ} {M N : GLₙFₚ n p}

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup : Group (GLₙFₚ n p) := Units.instGroup

def ZerosUnderDiag (M : GLₙFₚ n p) : Prop := ∀ i j, j < i → M.val i j = 0
def OnesOnDiag (M : GLₙFₚ n p) : Prop := ∀ i, M.val i i = 1

-- A predicate for upper triangular matrices
def IsUpperTriangular (M : GLₙFₚ n p) : Prop := ZerosUnderDiag M ∧ OnesOnDiag M

-- The product of two ut matrices has zeros under the diagonal
lemma ut_mul_zeros (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) (i j : Fin n) (h : j < i)
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

lemma zud_prod_0 {i j : Fin n} (hM : ZerosUnderDiag M) (hN : ZerosUnderDiag N) (h : j ≠ i)
   : (M.val i j) * (N.val j i) = 0 :=
    match ne_lt_or_ge h with
    | .inl h => by simp [hM i j h]
    | .inr h => by simp [hN j i h]

-- The product of two ut matrices has ones on the diagonal
lemma ut_mul_ones (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) (i : Fin n)
   : Matrix.dotProduct (λ k ↦ M.val i k) (λ k ↦ N.val k i) = 1 := by simp [
      Matrix.dotProduct,
      Finset.sum_eq_single_of_mem i
        (Finset.mem_univ i)
        (λ _ _ h ↦ zud_prod_0 hM.left hN.left h),
      hM.right i, hN.right i
    ]

instance : Invertible M.val := Units.invertible M

lemma zud_block_triangular (hM : ZerosUnderDiag M) : Matrix.BlockTriangular M.val id := hM

-- The inverse of an zud matrix is a zud matrix
lemma zud_inv_zud (h₁ : ZerosUnderDiag M) : ZerosUnderDiag M⁻¹ :=
  λ i j h₂ ↦ by
    simp [Matrix.coe_units_inv M]
    exact (Matrix.blockTriangular_inv_of_blockTriangular (zud_block_triangular h₁) h₂)

-- The inverse of an ut matrix has ones on the diagonal
lemma ut_inv_ones {i : Fin n} (h : IsUpperTriangular M) : M.inv i i = 1 :=
  have h₁ : (M.inv * M) i i = 1 := by simp [M.inv_val, Matrix.one_apply_eq i]
  have h₂ : Matrix.dotProduct (λ k ↦ M.inv i k) (λ k ↦ M k i) = 1 := h₁
  have h₃ : Matrix.dotProduct (λ k ↦ M.inv i k) (λ k ↦ M k i) = M.inv i i * M i i :=
    Finset.sum_eq_single_of_mem i
      (Finset.mem_univ i)
      (λ j _ h₁ ↦ by
        have h' := zud_prod_0 (zud_inv_zud h.left) h.left h₁
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
def UpperTriangularₙₚ (n : ℕ) (p : ℕ) : Subgroup (GLₙFₚ n p) :=
  {
    carrier := IsUpperTriangular,
    mul_mem' := λ ha hb ↦ ⟨ut_mul_zeros ha hb, ut_mul_ones ha hb⟩,
    one_mem' := ⟨
      λ _ _ h ↦ Matrix.one_apply_ne (Ne.symm (Fin.ne_of_lt h)),
      Matrix.one_apply_eq
    ⟩,
    inv_mem' := λ h ↦ ⟨zud_inv_zud h.left, λ _ ↦ ut_inv_ones h⟩
  }

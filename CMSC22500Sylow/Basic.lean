import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Init.Order.Defs

def GLₙFₚ (n p : ℕ) := GL (Fin n) (ZMod p)

variable {n p : ℕ}

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup : Group (GLₙFₚ n p) := Units.instGroup

-- A predicate for upper triangular matrices
def IsUpperTriangular (M : GLₙFₚ n p) : Prop :=
  (∀ i j, j < i → M.val i j = 0) ∧ (∀ i, M.val i i = 1)

-- The product of two ut matrices has zeros under the diagonal
lemma ut_mul_zeros {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i j : Fin n) (h : j < i)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k j) = 0 :=
  Finset.sum_eq_zero (λ k _ ↦
    if hki : k < i then by simp [ha.left i k hki]
    else by simp [hb.left k j (lt_of_lt_of_le h (not_lt.mp hki))])

lemma ne_lt_or_ge {a b : Fin n} (h : a ≠ b) : a < b ∨ a > b :=
  match le_or_gt a b with
  | .inl h₁ => match lt_or_eq_of_le h₁ with
    | .inl h₂ => .inl h₂
    | .inr h₂ => absurd h₂ h
  | .inr h₁ => .inr h₁

lemma ne_prod_0 {i j : Fin n} {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (h : j ≠ i)
   : (a.val i j) * (b.val j i) = 0 :=
    match ne_lt_or_ge h with
    | .inl h => by simp [ha.left i j h]
    | .inr h => by simp [hb.left j i h]

-- The product of two ut matrices has ones on the diagonal
lemma ut_mul_ones {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i : Fin n)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k i) = 1 := by simp [
      Matrix.dotProduct,
      Finset.sum_eq_single_of_mem i
        (Finset.mem_univ i)
        (λ _ _ h ↦ ne_prod_0 ha hb h),
      ha.right i, hb.right i
    ]

-- The inverse of an ut matrix has zeros under the diagonal
lemma ut_inv_zeros {x : GLₙFₚ n p} {i j : Fin n} (h₁ : IsUpperTriangular x)
   (h₂ : j < i) : x.inv i j = 0 := sorry

-- The inverse of an ut matrix has ones on the diagonal
lemma ut_inv_ones {x : GLₙFₚ n p} {i : Fin n} (h₁ : IsUpperTriangular x) : x.inv i i = 1 := sorry

-- The subgroup of upper triangular matrices
def UpperTriangularₙₚ (n : ℕ) (p : ℕ) : Subgroup (GLₙFₚ n p) :=
  {
    carrier := IsUpperTriangular,
    mul_mem' := λ ha hb ↦ ⟨ut_mul_zeros ha hb, ut_mul_ones ha hb⟩,
    one_mem' := ⟨
      λ _ _ h ↦ Matrix.one_apply_ne (Ne.symm (Fin.ne_of_lt h)),
      Matrix.one_apply_eq
    ⟩,
    inv_mem' := λ h₁ ↦ ⟨λ _ _ h₂ ↦ ut_inv_zeros h₁ h₂, λ _ ↦ ut_inv_ones h₁⟩
  }

def GL₃F₅Group := @GLₙFₚGroup 3 5
#eval GL₃F₅Group.one -- the 3x3 identity matrix

import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Init.Order.Defs

def GLₙFₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] := GL (Fin n.val) (ZMod p)

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup {n : ℕ+} {p : ℕ} [Fact p.Prime] : Group (GLₙFₚ n p) := Units.instGroup

-- A predicate for upper triangular matrices
def IsUpperTriangular {n : ℕ+} {p : ℕ} [Fact p.Prime] (M : GLₙFₚ n p) : Prop :=
  (∀ i j, j < i → M.val i j = 0) ∧ (∀ i, M.val i i = 1)

-- The product of two ut matrices has zeros under the diagonal
lemma ut_mul_zeros {n : ℕ+} {p : ℕ} [Fact p.Prime] {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i j : Fin n) (h : j < i)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k j) = 0 :=
  Finset.sum_eq_zero (λ k _ ↦
    if hki : k < i then by simp [ha.left i k hki]
    else by simp [hb.left k j (lt_of_lt_of_le h (not_lt.mp hki))])

lemma ne_lt_or_ge {n : ℕ+} {a b : Fin n.val} (h : a ≠ b) : a < b ∨ a > b := sorry

-- The product of two ut matrices has ones on the diagonal
lemma ut_mul_ones {n : ℕ+} {p : ℕ} [Fact p.Prime] {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i : Fin n)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k i) = 1 := by simp [
      Matrix.dotProduct,
      Finset.sum_eq_single_of_mem i
        (Finset.mem_univ i)
        ((λ j _ h ↦ match ne_lt_or_ge h with
          | .inl h₁ => by simp [ha.left i j h₁]
          | .inr h₁ => by simp [hb.left j i h₁])
        : ∀ j ∈ Finset.univ, j ≠ i → (a.val i j) * (b.val j i) = 0),
      ha.right i, hb.right i
    ]

-- The inverse of an ut matrix has zeros under the diagonal
lemma ut_inv_zeros {n : ℕ+} {p : ℕ} [Fact p.Prime] {x : GLₙFₚ n p}
  (h : IsUpperTriangular x) (i j : Fin n) (h : j < i) : x.inv i j = 0 := sorry

-- The inverse of an ut matrix has ones on the diagonal
lemma ut_inv_ones {n : ℕ+} {p : ℕ} [Fact p.Prime] {x : GLₙFₚ n p}
  (h : IsUpperTriangular x) (i : Fin n) : x.inv i i = 1 := sorry

-- The subgroup of upper triangular matrices
def UpperTriangularₙₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] : Subgroup (GLₙFₚ n p) :=
  {
    carrier := IsUpperTriangular,
    mul_mem' := λ ha hb ↦ ⟨ut_mul_zeros ha hb, ut_mul_ones ha hb⟩,
    one_mem' := ⟨
      λ _ _ h ↦ Matrix.one_apply_ne (Ne.symm (Fin.ne_of_lt h)),
      Matrix.one_apply_eq
    ⟩,
    inv_mem' := λ h ↦ ⟨ut_inv_zeros h, ut_inv_ones h⟩
  }

def GL₃F₅Group := @GLₙFₚGroup 3 5 (Fact.mk Nat.prime_five)
#eval GL₃F₅Group.one -- the 3x3 identity matrix

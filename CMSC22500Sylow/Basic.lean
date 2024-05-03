import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn

def GLₙFₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] := GL (Fin n.val) (ZMod p)

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup {n : ℕ+} {p : ℕ} [Fact p.Prime] : Group (GLₙFₚ n p) := Units.instGroup

-- A predicate for upper triangular matrices
def IsUpperTriangular {n : ℕ+} {p : ℕ} [Fact p.Prime] (M : GLₙFₚ n p) : Prop :=
  (∀ i j, j < i → M.val i j = 0) ∧ (∀ i, M.val i i = 1)

lemma ut_mul_zeros {n : ℕ+} {p : ℕ} [Fact p.Prime] {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i j : Fin n) (h : j < i)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k j) = 0 := sorry
  -- When k < i, the lhs of the multiplication is zero
  -- When k ≥ i → j < k, the rhs of the multiplication is zero
  --  → We are summing a bunch of zeros, so we get zero

lemma ut_mul_ones {n : ℕ+} {p : ℕ} [Fact p.Prime] {a b : GLₙFₚ n p}
  (ha : IsUpperTriangular a) (hb : IsUpperTriangular b) (i : Fin n)
   : Matrix.dotProduct (λ k ↦ a.val i k) (λ k ↦ b.val k i) = 1 := sorry
  -- When k < i, the lhs of the multiplication is zero
  -- When k > i, the rhs of the multiplication is zero
  -- When k = i, both sides of the multiplication are one
  --  → We are summing a bunch of zeros and a single one, so we get one

-- The subgroup of upper triangular matrices
def UpperTriangularₙₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] : Subgroup (GLₙFₚ n p) :=
  {
    carrier := IsUpperTriangular,
    mul_mem' := λ ha hb ↦ ⟨ut_mul_zeros ha hb, ut_mul_ones ha hb⟩,
    one_mem' := ⟨
      λ i j h ↦ Matrix.one_apply_ne (Ne.symm (Fin.ne_of_lt h)),
      Matrix.one_apply_eq
    ⟩,
    inv_mem' := λ ⟨h₁, h₂⟩ ↦ ⟨
      λ i j h ↦ sorry,
      λ i ↦ sorry,
    ⟩
  }

def GL₃F₅Group := @GLₙFₚGroup 3 5 (Fact.mk Nat.prime_five)
#eval GL₃F₅Group.one -- the 3x3 identity matrix

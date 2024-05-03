import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn

def GLₙFₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] := GL (Fin n) (ZMod p)

-- `GLₙFₚ n p` is a group
instance GLₙFₚGroup {n : ℕ+} {p : ℕ} [Fact p.Prime] : Group (GLₙFₚ n p) := Units.instGroup

-- A predicate for upper triangular matrices
def IsUpperTriangular {n : ℕ+} {p : ℕ} [Fact p.Prime] (M : GLₙFₚ n p) : Prop :=
  (∀ i j, j < i → M.val i j = 0) ∧ (∀ i, M.val i i = 1)

-- The subgroup of upper triangular matrices
def UpperTriangularₙₚ (n : ℕ+) (p : ℕ) [Fact p.Prime] : Subgroup (GLₙFₚ n p) :=
  {
    carrier := IsUpperTriangular,
    mul_mem' := sorry, -- We have to prove that multiplication is closed,
    one_mem' := sorry, -- that this subset contains the identity
    inv_mem' := sorry, -- and that taking inverses is closed
  }

def gp := @GLₙFₚGroup 3 5 (Fact.mk Nat.prime_five)
#eval gp.one -- the 3x3 identity matrix

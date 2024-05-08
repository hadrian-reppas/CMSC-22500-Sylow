import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

-- `GLₙFₚ n p` is the set of invertible `n` by `n` matrices with elements from `Fₚ`
abbrev GLₙFₚ (n p : ℕ) := GL (Fin n) (ZMod p)

-- `GLₙFₚ n p` is a group
instance {n p : ℕ} : Group (GLₙFₚ n p) := Units.instGroup

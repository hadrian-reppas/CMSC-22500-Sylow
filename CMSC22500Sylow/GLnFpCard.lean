import CMSC22500Sylow.GLnFp

-- https://people.math.osu.edu/cueto.5/teaching/6111/Au20/files/HW03Solutions.pdf
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset.html#Subgroup.card_subgroup_dvd_card
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Perm.html#Fintype.card_perm
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent.html

lemma GLₙFₚ_card (n p : ℕ) [Fact p.Prime] : Fintype.card (GLₙFₚ n p) = Finset.prod (Finset.range n) (λ i ↦ p ^ n - p ^ i) := sorry

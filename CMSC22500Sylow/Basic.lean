import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Multiplicity

import CMSC22500Sylow.GLnFp
import CMSC22500Sylow.GLnFpCard
import CMSC22500Sylow.SubgroupGLnFp
import CMSC22500Sylow.Unitriangular
import CMSC22500Sylow.UnitriangularCard
import CMSC22500Sylow.CardEq

def GLₙFₚSylow (n p : ℕ) [Fact p.Prime] : Sylow p (GLₙFₚ n p) := Sylow.ofCard (Unitriangularₙₚ n p) card_eq

-- Calegari's lemma: If `H ⊆ G`, `Γ ≃ H` and `P` is a `p`-Sylow of `G`, then we can
-- construct a `p`-Sylow of `Γ`.
lemma Calegari'sLemma (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] (H : Subgroup G)
  (Γ : Type v) [Group Γ] (h : Γ ≃* H) (P : Sylow p G) : Sylow p Γ := sorry

-- Sylow I
theorem SylowI (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Fintype G] [DecidableEq G] : Sylow p G :=
  Calegari'sLemma p (GLₙFₚ (Fintype.card G) p) (GLₙFₚ_hom G p).range G (subgroup_GLₙFₚ p G) (GLₙFₚSylow (Fintype.card G) p)

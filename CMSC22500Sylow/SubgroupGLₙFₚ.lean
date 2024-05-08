import Mathlib.Data.Nat.Prime
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Init.Order.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Sylow

import CMSC22500Sylow.GLₙFₚ

-- Some variables to make our life easier
universe u v
variable {G : Type u} [hg : Group G] [hft : Fintype G] [hdeq : DecidableEq G]
variable {n p : ℕ} [Fact p.Prime] {M N : GLₙFₚ n p}

-- A square matrix indexed by `Fin (Fintype.card G)`
abbrev FinMat (G : Type u) (α : Type v) [Fintype G] := Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) α

-- The injection from a permutation `σ : Equiv.Perm G` to a permutation matrix
def perm_mat₀ (σ : Equiv.Perm G) : Matrix G G (ZMod p) := λ i j ↦ if σ j = i then 1 else 0

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
noncomputable def perm_mat (G : Type u) (p : ℕ) [Group G] [Fintype G] [DecidableEq G] [Fact p.Prime]
   : MonoidHom (Equiv.Perm G) ((GLₙFₚ (Fintype.card G)) p) := {
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

-- `perm_mat` has trivial kernel
lemma perm_mat_trivial_ker [Fact p.Prime] : (perm_mat G p).ker = ⊥ := by
  refine (Subgroup.ext ?h).symm
  intro σ
  apply Iff.intro <;> intro h <;> simp at *
  · exact Subgroup.instCompleteLatticeSubgroup.proof_9 (MonoidHom.ker (perm_mat G p)) σ h
  · have h₁ : (perm_mat G p σ) = 1 := h
    have h₂ : ∀ i j, perm_mat G p σ i j = (1 : GLₙFₚ (Fintype.card G) p) i j := by
      intro _ _
      apply congrFun
      apply congrFun
      simp
      assumption
    ext x
    unfold perm_mat at h₁
    simp at h₁
    unfold perm_mat_fun at h₁
    have h₃ : perm_mat_reindexed σ = 1 := Units.eq_iff.mpr h₁
    unfold perm_mat_reindexed at h₃
    unfold reindex_hom at h₃
    unfold perm_mat₀_hom at h₃
    unfold perm_mat₀ at h₃
    unfold reindex at h₃
    simp at *
    unfold Matrix.submatrix at h₃
    simp at *
    let f := (enumerate G).symm
    have hf : (enumerate G).symm = f := rfl
    rw [hf] at h₃
    have h₄ : ∀ i j, (Matrix.of fun i j ↦ if σ (f j) = f i then 1 else 0) i j = (1 : FinMat G (ZMod p)) i j := λ i j ↦ h₂ i j
    have h₅ := h₄ (f.invFun x) (f.invFun x)
    simp at h₅
    assumption

-- `perm_mat` is injective
lemma perm_mat_inj [Fact p.Prime] : Function.Injective (perm_mat G p) :=
  (MonoidHom.ker_eq_bot_iff (perm_mat G p)).mp perm_mat_trivial_ker

-- `Equiv.Perm G` is isomorphic to a subgroup of `GLₙFₚ (Fintype.card G) p`
theorem perm_subgroup [Fact p.Prime] : Equiv.Perm G ≃* (perm_mat G p).range := by
  refine MonoidHom.ofInjective perm_mat_inj

theorem Cayley'sTheorem (G : Type u) [Group G] : G ≃* (MulAction.toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

-- The homomorphism that maps from `G` to `GLₙFₚ (Fintype.card G) p`
noncomputable def GLₙFₚ_hom (G : Type u) (p : ℕ) [Group G] [DecidableEq G] [Fintype G] [Fact p.Prime]
   : MonoidHom G (GLₙFₚ (Fintype.card G) p) := MonoidHom.comp (perm_mat G p) (MulAction.toPermHom G G)

-- `GLₙFₚ_hom` is injective
theorem GLₙFₚ_hom_inj [Fact p.Prime] : Function.Injective (GLₙFₚ_hom G p) := by
  unfold GLₙFₚ_hom
  unfold MonoidHom.comp
  simp
  apply Function.Injective.comp
  · exact perm_mat_inj
  · unfold MulAction.toPermHom
    simp
    unfold MulAction.toPerm
    simp
    intro σ τ
    simp
    intro h₁ _
    have h₂ := congrFun h₁ 1
    simp at h₂
    assumption

-- The final result: `G` is isomorphic to a subgroup of `GLₙFₚ (Fintype.card G) p`
theorem subgroup_GLₙFₚ (p : ℕ) (G : Type u) [Group G] [Fintype G] [DecidableEq G] [Fact p.Prime] : G ≃* (GLₙFₚ_hom G p).range := by
  refine MonoidHom.ofInjective GLₙFₚ_hom_inj

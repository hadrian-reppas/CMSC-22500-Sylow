import CMSC22500Sylow.GLₙFₚ
import CMSC22500Sylow.Unitriangularₙₚ

variable {n p : ℕ} [Fact p.Prime]

def IsAboveDiag (n : ℕ) (p : Fin n × Fin n) : Prop := p.fst < p.snd
def AboveDiag (n : ℕ) := { p : Fin n × Fin n // IsAboveDiag n p }

instance : Fintype (Fin n) := Fin.fintype n
instance : Fintype (Fin n × Fin n) := instFintypeProd (Fin n) (Fin n)
noncomputable instance : DecidablePred (@IsAboveDiag n) := Classical.decPred (IsAboveDiag n)
noncomputable instance : Fintype (AboveDiag n) := Subtype.fintype (@IsAboveDiag n)

def AboveDiag_equiv_impl (f : AboveDiag n → (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p) :=
  λ i j ↦ if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

lemma AboveDiag_ut (f : AboveDiag n → (ZMod p)) : (AboveDiag_equiv_impl f).BlockTriangular id := by
  intro i j h
  unfold AboveDiag_equiv_impl
  simp at *
  rw [if_neg]
  · have hn : ¬i < j := not_lt_of_gt h
    exact (Ne.dite_eq_right_iff fun h _ ↦ hn h).mpr hn
  · exact Fin.ne_of_gt h

lemma det_1 (f : AboveDiag n → (ZMod p)) : (AboveDiag_equiv_impl f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (AboveDiag_ut f)]
  unfold AboveDiag_equiv_impl
  simp

instance inv_f (f : AboveDiag n → (ZMod p)) [Fact p.Prime] : Invertible (AboveDiag_equiv_impl f) := by
  have : Invertible (AboveDiag_equiv_impl f).det := by
    rw [det_1]
    exact invertibleOne
  apply Matrix.invertibleOfDetInvertible (AboveDiag_equiv_impl f)

def AboveDiag_equiv₀ (f : AboveDiag n → (ZMod p)) [Fact p.Prime] : GLₙFₚ n p := {
  val := AboveDiag_equiv_impl f,
  inv := (inv_f f).invOf,
  val_inv := (inv_f f).mul_invOf_self,
  inv_val := (inv_f f).invOf_mul_self,
}

lemma beep_boop [Fact p.Prime] (f : AboveDiag n → (ZMod p)) : AboveDiag_equiv₀ f ∈ UpperTriangularₙₚ n p := by
  constructor
  · intro i j h
    unfold AboveDiag_equiv₀
    unfold AboveDiag_equiv_impl
    simp
    rw [if_neg]
    · have hn : ¬i < j := not_lt_of_gt h
      exact (Ne.dite_eq_right_iff fun h _ ↦ hn h).mpr hn
    · exact Fin.ne_of_gt h
  · intro i
    unfold AboveDiag_equiv₀
    unfold AboveDiag_equiv_impl
    simp

def AboveDiag_equiv' (f : AboveDiag n → (ZMod p)) : UpperTriangularₙₚ n p := {
  val := AboveDiag_equiv₀ f,
  property := beep_boop f,
}

def AboveDiag_inv (M : UpperTriangularₙₚ n p) (q : AboveDiag n) : (ZMod p) :=
  M.val q.val.fst q.val.snd

lemma left_inv (n p : ℕ) [hp : Fact p.Prime] : Function.LeftInverse (@AboveDiag_inv n p hp) (@AboveDiag_equiv' n p hp) := by
  refine Function.leftInverse_iff_comp.mpr ?_
  unfold AboveDiag_equiv'
  unfold AboveDiag_equiv₀
  unfold AboveDiag_equiv_impl
  unfold AboveDiag_inv
  ext f x
  simp
  unfold AboveDiag at *
  unfold IsAboveDiag at *
  have h₁ := x.property
  by_cases h₂ : x.val.fst = x.val.snd
  · rw [h₂] at h₁
    exact (gt_irrefl x.val.2 h₁).elim
  · refine ite_eq_iff.mpr ?_
    exact .inr (by
      constructor
      · assumption
      · refine ite_eq_iff.mpr ?_
        exact .inl (by
          constructor
          · assumption
          · rfl))

lemma fin_le_helper {i j : Fin n} (h₁ : ¬i = j) (h₂ : ¬i < j) : j < i := by
  refine Lean.Omega.Fin.not_le.mp ?_
  intro h
  exact (match LE.le.eq_or_lt h with
    | .inl h => (h₁ h).elim
    | .inr h => (h₂ h).elim)

lemma right_inv (n p : ℕ) [hp : Fact p.Prime] : Function.RightInverse (@AboveDiag_inv n p hp) (@AboveDiag_equiv' n p hp) := by
  refine Function.rightInverse_iff_comp.mpr ?_
  unfold AboveDiag_equiv'
  unfold AboveDiag_equiv₀
  unfold AboveDiag_equiv_impl
  unfold AboveDiag_inv
  ext M i j
  simp
  refine ite_eq_iff.mpr ?_
  by_cases h₁ : i = j
  · constructor
    constructor
    · assumption
    · rw [h₁]
      exact (M.property.right j).symm
  · exact .inr (by
      constructor
      · assumption
      · refine ite_eq_iff.mpr ?_
        by_cases h₂ : i < j
        · constructor
          constructor
          · assumption
          · rfl
        · exact .inr (by
            constructor
            · assumption
            · have h₃ : j < i := fin_le_helper h₁ h₂
              exact (M.property.left i j h₃).symm))

def AboveDiag_equiv (n p : ℕ) [Fact p.Prime] : (AboveDiag n → ZMod p) ≃ UpperTriangularₙₚ n p := {
  toFun := AboveDiag_equiv',
  invFun := AboveDiag_inv,
  left_inv := left_inv n p,
  right_inv := right_inv n p,
}

-- TODO
lemma AboveDiag_card (n : ℕ) : Fintype.card (AboveDiag n) = n * (n - 1) / 2 := sorry

lemma ZMod_card (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p) = p := ZMod.card p
noncomputable instance fin_funs {n : ℕ} [Fact p.Prime] : Fintype (AboveDiag n → ZMod p) := Fintype.ofFinite (AboveDiag n → ZMod p)
noncomputable instance AboveDiag_DecidableEq {n : ℕ} : DecidableEq (AboveDiag n) := Classical.typeDecidableEq (AboveDiag n)
lemma AboveDiag_fun_card (n p : ℕ) [Fact p.Prime] : Fintype.card (AboveDiag n → ZMod p) = p ^ (n * (n - 1) / 2) := by
  rw [Fintype.card_fun, ZMod.card p, AboveDiag_card]
noncomputable instance [Fact p.Prime] : Fintype (UpperTriangularₙₚ n p) := Fintype.ofFinite (UpperTriangularₙₚ n p)

-- Yay!
lemma UT_card (n p : ℕ) [Fact p.Prime] : Fintype.card (UpperTriangularₙₚ n p) = p ^ (n * (n - 1) / 2) := by
  rw [←Fintype.card_congr (AboveDiag_equiv n p)]
  exact AboveDiag_fun_card n p

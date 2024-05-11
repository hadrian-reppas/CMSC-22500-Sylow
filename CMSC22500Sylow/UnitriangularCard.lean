import CMSC22500Sylow.GLnFp
import CMSC22500Sylow.Unitriangular

variable {n p : ℕ} [Fact p.Prime]

def IsAboveDiag (n : ℕ) (p : Fin n × Fin n) : Prop := p.fst < p.snd
def AboveDiag (n : ℕ) := { p : Fin n × Fin n // IsAboveDiag n p }

instance : Fintype (Fin n) := Fin.fintype n
instance : Fintype (Fin n × Fin n) := instFintypeProd (Fin n) (Fin n)
noncomputable instance : DecidablePred (@IsAboveDiag n) := Classical.decPred (IsAboveDiag n)
noncomputable instance : Fintype (AboveDiag n) := Subtype.fintype (@IsAboveDiag n)
noncomputable instance : DecidableEq (AboveDiag n) := Classical.typeDecidableEq (AboveDiag n)

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

lemma beep_boop [Fact p.Prime] (f : AboveDiag n → (ZMod p)) : AboveDiag_equiv₀ f ∈ Unitriangularₙₚ n p := by
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

def AboveDiag_equiv' (f : AboveDiag n → (ZMod p)) : Unitriangularₙₚ n p := {
  val := AboveDiag_equiv₀ f,
  property := beep_boop f,
}

def AboveDiag_inv (M : Unitriangularₙₚ n p) (q : AboveDiag n) : (ZMod p) :=
  M.val q.val.fst q.val.snd

lemma left_inv' (n p : ℕ) [hp : Fact p.Prime] : Function.LeftInverse (@AboveDiag_inv n p hp) (@AboveDiag_equiv' n p hp) := by
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

lemma right_inv' (n p : ℕ) [hp : Fact p.Prime] : Function.RightInverse (@AboveDiag_inv n p hp) (@AboveDiag_equiv' n p hp) := by
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

def AboveDiag_equiv (n p : ℕ) [Fact p.Prime] : (AboveDiag n → ZMod p) ≃ Unitriangularₙₚ n p := {
  toFun := AboveDiag_equiv',
  invFun := AboveDiag_inv,
  left_inv := left_inv' n p,
  right_inv := right_inv' n p,
}

def lift {n : ℕ} (i : AboveDiag n) : AboveDiag n.succ := ⟨(i.val.fst, i.val.snd), by
  have h := i.property
  unfold IsAboveDiag at *
  simp at *
  assumption⟩

def lift_inj : Function.Injective (@lift n) := by
  intros x y h
  unfold lift at *
  simp at *
  unfold AboveDiag at *
  unfold Fin.castSucc at *
  unfold Fin.castAdd at *
  simp at *
  apply Subtype.eq
  exact Prod.ext h.left h.right

lemma baz₀ {a b : ℕ} (hb : Even b) : a / 2 + b / 2 = (a + b) / 2 := by
  refine (Nat.add_div_of_dvd_left ?hca).symm
  exact even_iff_two_dvd.mp hb

lemma baz (n : ℕ) : n + n * (n - 1) / 2 = n.succ * n / 2 := by
  calc
    n + n * (n - 1) / 2         = n * 2 / 2 + n * (n - 1) / 2 := by
      have h₁ : n = n * 2 / 2 := by refine Nat.eq_div_of_mul_eq_left ?hc rfl; simp
      nth_rewrite 1 [h₁]
      rfl
    n * 2 / 2 + n * (n - 1) / 2 = (n * 2 + n * (n - 1)) / 2   := by
      have h₁ : Even (n * (n - 1)) := Nat.even_mul_pred_self n
      exact baz₀ h₁
    (n * 2 + n * (n - 1)) / 2   = n * (2 + (n - 1)) / 2       := by rw [Nat.left_distrib]
    n * (2 + (n - 1)) / 2       = n * (n + 1) / 2             := by
      cases n
      case zero => rfl
      case succ n' =>
        simp
        have h₁ : n'.succ + 1 = 2 + n' := by linarith
        rw [h₁]
    n * (n + 1) / 2             = (n + 1) * n / 2             := by rw [Nat.mul_comm]

lemma cp {P Q : Prop} (h : P ↔ Q) : ¬P ↔ ¬Q := by exact not_congr h

lemma blah {a b : ℕ} (h₁ : a < b) (h₂ : b < a.succ) : False :=
  have h₃ : b ≤ a := Nat.le_of_lt_succ h₂
  have h₄ : ¬a < b := Nat.not_lt.mpr h₃
  h₄ h₁

def blingo {k : ℕ} (x : Fin k) : AboveDiag k.succ := {
  val := (Fin.mk x (Fin.find.proof_6 k x), Fin.last k),
  property := by
    unfold IsAboveDiag at *
    unfold Fin.last
    simp
}

lemma blingo_inj {k : ℕ} : Function.Injective (@blingo k) := by
  intro x y h
  unfold blingo at *
  have h₁ := congrArg Subtype.val h
  simp at *
  exact Fin.eq_of_val_eq h₁

lemma image_card (k : ℕ) : (Finset.image (@lift k) Finset.univ)ᶜ.card = k := by
  let im := Finset.image (@lift k) Finset.univ
  have imh : Finset.image (@lift k) Finset.univ = im := rfl
  rw [imh]
  have h₁ : ∀ y, y.val.snd < k ↔ y ∈ im := by
    intro y
    apply Iff.intro
    · intro h
      refine Finset.mem_image.mpr ?_
      let x : AboveDiag k := ⟨
        (
          ⟨y.val.fst.val, by
            have h₁ := y.property
            unfold IsAboveDiag at *
            exact Nat.lt_trans h₁ h⟩,
          ⟨y.val.snd.val, by assumption⟩,
        ),
        by
          unfold AboveDiag at *
          unfold IsAboveDiag at *
          have h := y.property
          simp at *
          assumption
      ⟩
      existsi x
      constructor
      · exact Finset.mem_univ x
      · unfold lift; simp
    · intro h
      by_contra! h'
      have ⟨x, ⟨_, hx⟩⟩ := Finset.mem_image.mp h
      unfold lift at hx
      simp at *
      have h₂ := congrArg Subtype.val hx
      have h₃ := congrArg Prod.snd h₂
      simp at *
      have h₄ := Fin.castSucc_lt_last x.val.2
      rw [h₃] at h₄
      have h₅ : k < ↑(Fin.last k) := LE.le.trans_lt h' h₄
      unfold Fin.last at h₅
      simp at h₅
  have h₂ : ∀ y, y.val.snd = k ↔ y ∈ imᶜ := by
    intro y
    apply Iff.intro <;> intro h
    · have h₃ : ¬y.val.2.val < k := eq_iff_not_lt_of_le.mp λ _ ↦ id h.symm
      have h₄ := (cp (h₁ y)).mp h₃
      simp
      exact h₄
    · have h₃ : ¬y ∈ im := Finset.mem_compl.mp h
      have h₄ := (cp (h₁ y)).mpr h₃
      have h₅ : y.val.2.val ≥ k := Nat.le_of_not_lt h₄
      cases Nat.lt_or_eq_of_le h₅
      case inl h₆ =>
        exfalso
        have h₇ := y.val.snd.isLt
        exact blah h₆ h₇
      case inr h₆ => exact h₆.symm
  have h₃ : Finset.image (@blingo k) Finset.univ = imᶜ := by
    refine Finset.ext_iff.mpr ?_
    intro y
    apply Iff.intro <;> intro h
    · apply (h₂ y).mp
      have h₃ : ∀ x ∈ (@Finset.univ (Fin k) instFintypeFin), (blingo x).val.snd.val = k := by
        intro x _
        unfold blingo
        simp
      have h₄ : (∀ b ∈ Finset.image (@blingo k) Finset.univ, b.val.snd.val = k) := Finset.forall_image.mpr h₃
      exact h₄ y h
    · have h₃ := (h₂ y).mpr h
      apply Finset.mem_image.mpr
      let x : Fin k := ⟨y.val.1.val, by
        have h₄ := y.property
        unfold IsAboveDiag at h₄
        have h₅ : y.val.1.val < y.val.2.val := by exact h₄
        rw [h₃] at h₅
        assumption⟩
      existsi x
      constructor
      · exact Finset.mem_univ x
      · unfold blingo
        unfold Fin.last
        simp at *
        apply Subtype.eq
        simp at *
        apply Prod.ext
        · simp
        · simp
          apply Fin.eq_of_val_eq
          simp
          exact h₃.symm
  have h₄ : Finset.card (Finset.univ : Finset (Fin k)) = k := Finset.card_fin k
  have h₅ := Finset.card_image_of_injective Finset.univ (@blingo_inj k)
  rw [←h₃]
  rw [h₅]
  assumption

lemma AboveDiag_card (n : ℕ) : Fintype.card (AboveDiag n) = n * (n - 1) / 2 := by
  induction n
  case zero => rfl
  case succ k ih =>
    simp
    let im := Finset.image (@lift k) Finset.univ
    have h₁ := Finset.card_image_of_injective Finset.univ (@lift_inj k)
    rw [Finset.card_univ, ih] at h₁
    have imh : Finset.image (@lift k) Finset.univ = im := rfl
    rw [imh] at h₁
    have h₂ := Finset.card_compl_add_card im
    rw [h₁] at h₂
    rw [←h₂, image_card k]
    exact baz k

lemma ZMod_card (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p) = p := ZMod.card p
noncomputable instance fin_funs {n : ℕ} [Fact p.Prime] : Fintype (AboveDiag n → ZMod p) := Fintype.ofFinite (AboveDiag n → ZMod p)
noncomputable instance AboveDiag_DecidableEq {n : ℕ} : DecidableEq (AboveDiag n) := Classical.typeDecidableEq (AboveDiag n)
lemma AboveDiag_fun_card (n p : ℕ) [Fact p.Prime] : Fintype.card (AboveDiag n → ZMod p) = p ^ (n * (n - 1) / 2) := by
  rw [Fintype.card_fun, ZMod.card p, AboveDiag_card]
noncomputable instance [Fact p.Prime] : Fintype (Unitriangularₙₚ n p) := Fintype.ofFinite (Unitriangularₙₚ n p)

-- Yay!
lemma Unitriangular_card (n p : ℕ) [Fact p.Prime] : Fintype.card (Unitriangularₙₚ n p) = p ^ (n * (n - 1) / 2) := by
  rw [←Fintype.card_congr (AboveDiag_equiv n p)]
  exact AboveDiag_fun_card n p

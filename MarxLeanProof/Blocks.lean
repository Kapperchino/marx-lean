module
public import MarxLeanProof.Productivity
public import MarxLeanProof.Accounting
@[expose] public section
set_option autoImplicit false

/-! # Block production and exact elimination (Theorem 6.1, A.1, C.5) -/
namespace Research
open Matrix
open scoped BigOperators Research
set_option linter.unusedSectionVars false
variable {n m o : Type*} [Fintype n] [Fintype m] [Fintype o]
  [DecidableEq n] [DecidableEq m] [DecidableEq o]

lemma block_complement (A : Matrix n n ℝ) (F : Matrix n m ℝ)
    (H : Matrix m n ℝ) (T : Matrix m m ℝ) :
    1 - fromBlocks A F H T = fromBlocks (1 - A) (-F) (-H) (1 - T) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.fromBlocks, Matrix.sub_apply]

/-- The inverse in equation C.10, verified on both sides. -/
theorem augmented_inverse {A : Matrix n n ℝ} (P : Productive A)
    (F : Matrix n m ℝ) (H : Matrix m n ℝ) (T : Matrix m m ℝ)
    (Q : Productive (H * P.N * F + T)) :
    let K := fromBlocks (P.N + P.N * F * Q.N * H * P.N) (P.N * F * Q.N)
      (Q.N * H * P.N) Q.N
    K * (1 - fromBlocks A F H T) = 1 ∧ (1 - fromBlocks A F H T) * K = 1 := by
  dsimp only
  rw [block_complement]
  have h11 : (P.N + P.N * F * Q.N * H * P.N) * (1 - A) +
      (P.N * F * Q.N) * (-H) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_neg, Matrix.mul_assoc]
    rw [P.inverse_mul, Matrix.mul_one]
    abel
  have h12 : (P.N + P.N * F * Q.N * H * P.N) * (-F) +
      (P.N * F * Q.N) * (1 - T) = 0 := by
    calc
      _ = P.N * F * (Q.N * (1 - (H * P.N * F + T)) - 1) := by
        simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg,
          Matrix.mul_one, Matrix.mul_assoc]
        abel
      _ = 0 := by rw [Q.inverse_mul, sub_self, Matrix.mul_zero]
  have h21 : Q.N * H * P.N * (1 - A) + Q.N * (-H) = 0 := by
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
    rw [P.inverse_mul, Matrix.mul_one]
    abel
  have h22 : Q.N * H * P.N * (-F) + Q.N * (1 - T) = 1 := by
    calc
      _ = Q.N * (1 - (H * P.N * F + T)) := by
        simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_assoc]
        abel
      _ = 1 := Q.inverse_mul
  have g11 : (1 - A) * (P.N + P.N * F * Q.N * H * P.N) +
      (-F) * (Q.N * H * P.N) = 1 := by
    calc
      _ = (1 - A) * P.N + (((1 - A) * P.N) * F - F) * Q.N * H * P.N := by
        simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc]
        abel
      _ = 1 := by simp [P.mul_inverse]
  have g12 : (1 - A) * (P.N * F * Q.N) + (-F) * Q.N = 0 := by
    calc
      _ = (((1 - A) * P.N) * F - F) * Q.N := by
        simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc]
        abel
      _ = 0 := by simp [P.mul_inverse]
  have g21 : (-H) * (P.N + P.N * F * Q.N * H * P.N) +
      (1 - T) * (Q.N * H * P.N) = 0 := by
    calc
      _ = ((1 - (H * P.N * F + T)) * Q.N - 1) * (H * P.N) := by
        simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul,
          Matrix.one_mul, Matrix.mul_assoc]
        abel
      _ = 0 := by rw [Q.mul_inverse, sub_self, Matrix.zero_mul]
  have g22 : (-H) * (P.N * F * Q.N) + (1 - T) * Q.N = 1 := by
    calc
      _ = (1 - (H * P.N * F + T)) * Q.N := by
        simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc]
        abel
      _ = 1 := Q.mul_inverse
  constructor
  · rw [fromBlocks_multiply, h11, h12, h21, h22, fromBlocks_one]
  · rw [fromBlocks_multiply, g11, g12, g21, g22, fromBlocks_one]

/-- C.5: productive goods and reproduction matrices imply a productive augmented system. -/
def Productive.augment {A : Matrix n n ℝ} (P : Productive A)
    {F : Matrix n m ℝ} {H : Matrix m n ℝ} {T : Matrix m m ℝ}
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (Q : Productive (H * P.N * F + T)) : Productive (fromBlocks A F H T) where
  nonneg := by intro i j; cases i <;> cases j
               exacts [P.nonneg _ _, hF _ _, hH _ _, hT _ _]
  N := fromBlocks (P.N + P.N * F * Q.N * H * P.N) (P.N * F * Q.N)
    (Q.N * H * P.N) Q.N
  inverse_nonneg := by
    have hnf := mm_nonneg P.inverse_nonneg hF
    have hnfz := mm_nonneg hnf Q.inverse_nonneg
    have hzh := mm_nonneg Q.inverse_nonneg hH
    intro i j; cases i <;> cases j
    · exact add_nonneg (P.inverse_nonneg _ _) (mm_nonneg (mm_nonneg hnfz hH) P.inverse_nonneg _ _)
    · exact hnfz _ _
    · exact mm_nonneg hzh P.inverse_nonneg _ _
    · exact Q.inverse_nonneg _ _
  inverse_mul := (augmented_inverse P F H T Q).1
  mul_inverse := (augmented_inverse P F H T Q).2

/-- The zero ordinary-input system is productive, in any finite dimension. -/
def zeroProductive : Productive (0 : Matrix n n ℝ) where
  nonneg := le_rfl
  N := 1
  inverse_nonneg := by intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  inverse_mul := by simp
  mul_inverse := by simp

/-- Theorem 6.1 allows any number of terminal copying/service activities. -/
def Productive.append {A : Matrix n n ℝ} (P : Productive A)
    {a : Matrix n o ℝ} (ha : 0 ≤ a) : Productive (fromBlocks A a 0 0) := by
  apply P.augment ha le_rfl le_rfl
  simpa only [Matrix.zero_mul, zero_add] using (zeroProductive : Productive (0 : Matrix o o ℝ))

/-- Equation (6.2), proved from the block labor equations. -/
theorem terminal_labor {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (a : Matrix n o ℝ) (h : Matrix m o ℝ) :
    let G : Matrix m (n ⊕ o) ℝ := Matrix.fromCols (P.labor H) (h + P.labor H * a)
    G = Matrix.fromCols H h + @HMul.hMul (Matrix m (n ⊕ o) ℝ)
      (Matrix (n ⊕ o) (n ⊕ o) ℝ) (Matrix m (n ⊕ o) ℝ)
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid G (fromBlocks A a 0 0) := by
  dsimp only
  rw [fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero]
  ext i j
  cases j with
  | inl j => exact congrFun (congrFun (P.labor_fixed H) i) j
  | inr j => rfl

/-- A principal block of a nonnegative productive matrix is productive. -/
noncomputable def Productive.external
    {A : Matrix n n ℝ} {B : Matrix n o ℝ} {C : Matrix o n ℝ} {D : Matrix o o ℝ}
    (P : Productive (fromBlocks A B C D)) : Productive D := by
  apply Classical.choice
  obtain ⟨w, hw, hAw⟩ := P.positive_witness
  have hD : 0 ≤ D := fun i j => P.nonneg (.inr i) (.inr j)
  have hC : 0 ≤ C := fun i j => P.nonneg (.inr i) (.inl j)
  refine ⟨productiveOfWitness hD (w ∘ Sum.inr) (fun i => hw (.inr i)) ?_⟩
  intro i
  have hi := hAw (.inr i)
  simp only [fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply] at hi
  have hn := mv_nonneg hC (fun j => (hw (.inl j)).le) i
  change 0 ≤ (C *ᵥ (w ∘ Sum.inl)) i at hn
  change (D *ᵥ (w ∘ Sum.inr)) i < w (.inr i)
  linarith

/-- A.1: exact elimination remains productive even with boundary feedback. -/
noncomputable def Productive.eliminate
    {A : Matrix n n ℝ} {B : Matrix n o ℝ} {C : Matrix o n ℝ} {D : Matrix o o ℝ}
    (P : Productive (fromBlocks A B C D)) (PO : Productive D) :
    Productive (A + B * PO.N * C) := by
  apply Classical.choice
  obtain ⟨w, hw, hAw⟩ := P.positive_witness
  have hA : 0 ≤ A := fun i j => P.nonneg (.inl i) (.inl j)
  have hB : 0 ≤ B := fun i j => P.nonneg (.inl i) (.inr j)
  have hC : 0 ≤ C := fun i j => P.nonneg (.inr i) (.inl j)
  have hCw : C *ᵥ (w ∘ Sum.inl) ≤ (1 - D) *ᵥ (w ∘ Sum.inr) := by
    intro i
    have hi := hAw (.inr i)
    simp only [fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply] at hi
    simp only [sub_mulVec, one_mulVec, Pi.sub_apply, Function.comp_apply]
    linarith
  have hW := mv_mono PO.inverse_nonneg hCw
  simp only [mulVec_mulVec, PO.inverse_mul, one_mulVec] at hW
  refine ⟨productiveOfWitness
    (add_nonneg hA (mm_nonneg (mm_nonneg hB PO.inverse_nonneg) hC))
    (w ∘ Sum.inl) (fun i => hw (.inl i)) ?_⟩
  intro i
  have hi := hAw (.inl i)
  simp only [fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply] at hi
  have hb := mv_mono hB hW i
  simp only [add_mulVec, ← mulVec_mulVec, Pi.add_apply]
  simpa! only [mulVec_mulVec, Function.comp_apply] using (add_le_add_right hb ((A *ᵥ (w ∘ Sum.inl)) i)).trans_lt hi

/-- The equivalent augmented equations in C.9, with the commodity equation
eliminated by the already verified labor identity. -/
theorem augmented_equations {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (F : Matrix n m ℝ) (T : Matrix m m ℝ)
    (α : m → ℝ) (κ : ℝ) :
    α - (P.labor H * F + T)ᵀ *ᵥ α = κ • (1 : m → ℝ) ↔
    α = Fᵀ *ᵥ ((P.labor H)ᵀ *ᵥ α) + Tᵀ *ᵥ α + κ • (1 : m → ℝ) := by
  rw [sub_eq_iff_eq_add]
  simp only [transpose_add, transpose_mul, add_mulVec, ← mulVec_mulVec]
  constructor <;> intro h <;> simpa only [add_assoc, add_left_comm, add_comm] using h

end Research

module
public import MarxLeanProof.Spectral
public import MarxLeanProof.Blocks
public import MarxLeanProof.Conversion
@[expose] public section
set_option autoImplicit false

/-! # Combined statements in the paper's spectral notation -/
namespace Research
open Matrix
open scoped Research
set_option linter.unusedSectionVars false
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The converse part of C.5, by eliminating ordinary goods. -/
noncomputable def Productive.reproductionBlock {A : Matrix n n ℝ} (P : Productive A)
    {F : Matrix n m ℝ} {H : Matrix m n ℝ} {T : Matrix m m ℝ}
    (Q : Productive (fromBlocks A F H T)) : Productive (H * P.N * F + T) := by
  have Qswap : Productive (fromBlocks T H F A) := by
    have he : (fromBlocks A F H T).submatrix (Equiv.sumComm m n) (Equiv.sumComm m n) =
        fromBlocks T H F A := by
      ext i j; cases i <;> cases j <;> rfl
    rw [← he]
    exact Q.reindex (Equiv.sumComm m n)
  simpa only [add_comm] using Qswap.eliminate P

/-- C.5, including both directions of augmented productivity. -/
theorem augmented_productive_iff {A : Matrix n n ℝ} (P : Productive A)
    {F : Matrix n m ℝ} {H : Matrix m n ℝ} {T : Matrix m m ℝ}
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    Nonempty (Productive (fromBlocks A F H T)) ↔ Nonempty (Productive (H * P.N * F + T)) := by
  constructor
  · rintro ⟨Q⟩; exact ⟨P.reproductionBlock Q⟩
  · rintro ⟨Q⟩; exact ⟨P.augment hF hH hT Q⟩

/-- C.5 in the PDF's spectral form. -/
theorem augmented_spectral_iff [Nonempty m] {A : Matrix n n ℝ} (P : Productive A)
    {F : Matrix n m ℝ} {H : Matrix m n ℝ} {T : Matrix m m ℝ}
    (hF : 0 ≤ F) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    SpectralProductive (fromBlocks A F H T) ↔ SpectralProductive (P.labor H * F + T) := by
  have hK : 0 ≤ fromBlocks A F H T := by
    intro i j; cases i <;> cases j
    exacts [P.nonneg _ _, hF _ _, hH _ _, hT _ _]
  rw [spectral_iff_productive hK,
    spectral_iff_productive (add_nonneg (mm_nonneg (P.labor_nonneg hH) hF) hT)]
  exact augmented_productive_iff P hF hH hT

/-- Theorem C.2: existence AND uniqueness are equivalent to ρ(M)<1. -/
theorem equalResidual_iff_spectral {M : Matrix m m ℝ} (hM : 0 ≤ M) (b : m) :
    (∃! aκ : (m → ℝ) × ℝ, EqualResidual M b aκ.1 aκ.2) ↔
      SpectralProductive M := by
  let : Nonempty m := ⟨b⟩
  have hMt : 0 ≤ Mᵀ := fun i j => hM j i
  constructor
  · rintro ⟨aκ, h, _⟩
    apply (spectral_transpose M).mp
    apply (spectral_iff_productive hMt).mpr
    exact ⟨productiveOfWitness hMt aκ.1 h.1 (Conversion.witness_of_equalResidual h)⟩
  · intro hs
    exact Conversion.existsUnique (productiveOfSpectral hMt ((spectral_transpose M).mpr hs)) b

/-- C.7: unnormalized multipliers are monotone in reproduction coefficients. -/
theorem beta_monotone {M M' : Matrix m m ℝ} (Q : Productive Mᵀ) (Q' : Productive M'ᵀ)
    (hMM : M ≤ M') : Conversion.beta Q ≤ Conversion.beta Q' := by
  have hi : (0 : Matrix m m ℝ) ≤ 1 := by
    intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  have hn : Q.N ≤ Q'.N := by
    simpa only [Productive.labor, Matrix.one_mul] using
      labor_monotone Q Q' hi (fun i j => hMM j i) (le_refl (1 : Matrix m m ℝ))
  intro i
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hn i j) zero_le_one

end Research

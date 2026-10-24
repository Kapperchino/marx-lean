module
public import MarxLeanProof.Conversion
@[expose] public section
set_option autoImplicit false

/-! # Physical and occupational unit transformations (3.6, C.6, C.9) -/
namespace Research
open Matrix
open scoped BigOperators Research
set_option linter.unusedSectionVars false
variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq m] [DecidableEq p]

lemma cancel_middle (A : Matrix m n ℝ) (S T : Matrix n n ℝ) (B : Matrix n p ℝ)
    (h : S * T = 1) : A * S * (T * B) = A * B := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc S T, h, Matrix.one_mul]

lemma conjugate_complement (A S T : Matrix n n ℝ) (hTS : T * S = 1) :
    1 - T * A * S = T * (1 - A) * S := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hTS]

/-- Physical units, Proposition 3.6: the transformed inverse is TNS. -/
def Productive.changeUnits {A : Matrix n n ℝ} (P : Productive A)
    (S T : Matrix n n ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S * T = 1) (hTS : T * S = 1) : Productive (T * A * S) where
  nonneg := mm_nonneg (mm_nonneg hT P.nonneg) hS
  N := T * P.N * S
  inverse_nonneg := mm_nonneg (mm_nonneg hT P.inverse_nonneg) hS
  inverse_mul := by
    rw [conjugate_complement A S T hTS, Matrix.mul_assoc T (1 - A) S,
      cancel_middle (T * P.N) S T ((1 - A) * S) hST,
      ← Matrix.mul_assoc, Matrix.mul_assoc T P.N (1 - A), P.inverse_mul,
      Matrix.mul_one, hTS]
  mul_inverse := by
    rw [conjugate_complement A S T hTS, Matrix.mul_assoc T P.N S,
      cancel_middle (T * (1 - A)) S T (P.N * S) hST,
      ← Matrix.mul_assoc, Matrix.mul_assoc T (1 - A) P.N, P.mul_inverse,
      Matrix.mul_one, hTS]

/-- G'=GS under the physical-unit transformation. -/
theorem labor_change_units {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (S T : Matrix n n ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (P.changeUnits S T hS hT hST hTS).labor (H * S) = P.labor H * S := by
  change H * S * (T * P.N * S) = H * P.N * S
  rw [Matrix.mul_assoc T P.N S, cancel_middle H S T (P.N * S) hST, Matrix.mul_assoc]

/-- Total occupational requirements do not depend on commodity units. -/
theorem demand_change_units (G : Matrix m n ℝ) (S T : Matrix n n ℝ)
    (hST : S * T = 1) (y : n → ℝ) : (G * S) *ᵥ (T *ᵥ y) = G *ᵥ y := by
  rw [mulVec_mulVec, Matrix.mul_assoc, hST, Matrix.mul_one]

/-- C.6: reproduction goods must change units along with ordinary production. -/
theorem reproduction_change_physical_units (G : Matrix m n ℝ) (F : Matrix n m ℝ)
    (U : Matrix m m ℝ) (S T : Matrix n n ℝ) (hST : S * T = 1) :
    (G * S) * (T * F) + U = G * F + U := by rw [cancel_middle G S T F hST]

/-- C.23: M transforms by similarity under occupational units. -/
theorem reproduction_change_labor_units (G : Matrix m n ℝ) (F : Matrix n m ℝ)
    (T J Jinv : Matrix m m ℝ) :
    (Jinv * G) * (F * J) + Jinv * T * J = Jinv * (G * F + T) * J := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- C.24: the residual source transforms with the occupation units. This identity
is valid for any invertible J; diagonal J is its time-unit specialization. -/
theorem residual_change_labor_units (M J Jinv : Matrix m m ℝ)
    (hJ : J * Jinv = 1) (α : m → ℝ) :
    Jᵀ *ᵥ α - (Jinv * M * J)ᵀ *ᵥ (Jᵀ *ᵥ α) = Jᵀ *ᵥ (α - Mᵀ *ᵥ α) := by
  have ht : Jinvᵀ * Jᵀ = 1 := by
    simpa only [transpose_mul, transpose_one] using congrArg Matrix.transpose hJ
  rw [transpose_mul, transpose_mul, mulVec_mulVec]
  have hm : (Jᵀ * (Mᵀ * Jinvᵀ)) * Jᵀ = Jᵀ * Mᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ht, Matrix.mul_one]
  rw [hm, mulVec_sub, mulVec_mulVec]

/-- Scalar output values are invariant in the same common-value unit. -/
theorem values_change_labor_units (G : Matrix m n ℝ) (J Jinv : Matrix m m ℝ)
    (hJ : J * Jinv = 1) (α : m → ℝ) :
    (Jinv * G)ᵀ *ᵥ (Jᵀ *ᵥ α) = Gᵀ *ᵥ α := by
  have ht : Jinvᵀ * Jᵀ = 1 := by
    simpa only [transpose_mul, transpose_one] using congrArg Matrix.transpose hJ
  rw [transpose_mul, mulVec_mulVec, Matrix.mul_assoc, ht, Matrix.mul_one]

/-- Positive unit changes and their inverse matrices. -/
def unitMatrix (t : m → ℝ) : Matrix m m ℝ := diagonal t
noncomputable def inverseUnitMatrix (t : m → ℝ) : Matrix m m ℝ := diagonal (fun i => (t i)⁻¹)

lemma unitMatrix_inverse {t : m → ℝ} (ht : ∀ i, 0 < t i) :
    unitMatrix t * inverseUnitMatrix t = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [unitMatrix, inverseUnitMatrix, (ht i).ne']
  · simp [unitMatrix, inverseUnitMatrix, h]

lemma inverse_unitMatrix {t : m → ℝ} (ht : ∀ i, 0 < t i) :
    inverseUnitMatrix t * unitMatrix t = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [unitMatrix, inverseUnitMatrix, (ht i).ne']
  · simp [unitMatrix, inverseUnitMatrix, h]

/-- The new weights are ti αi, so per-unit ratios acquire the factor ti/tj. -/
theorem labor_unit_ratio (t α : m → ℝ) (i j : m) :
    (unitMatrix t *ᵥ α) i / (unitMatrix t *ᵥ α) j =
      (t i / t j) * (α i / α j) := by
  simp only [unitMatrix, mulVec_diagonal]
  exact mul_div_mul_comm _ _ _ _

/-- Resetting the reference unit divides every common value by the same tb. -/
theorem reference_rebase (α : m → ℝ) (t : m → ℝ) (b : m)
    (hα : α b = 1) (ht : t b ≠ 0) :
    ((t b)⁻¹ • (unitMatrix t *ᵥ α)) b = 1 := by
  simp [unitMatrix, mulVec_diagonal, hα, ht]

/-- Strictly positive changes of physical units preserve numerical support. -/
theorem support_change_units {A : Matrix n n ℝ} {s : n → ℝ} (hs : ∀ i, 0 < s i)
    (i j : n) : 0 < (inverseUnitMatrix s * A * unitMatrix s) i j ↔ 0 < A i j := by
  simp only [inverseUnitMatrix, unitMatrix, diagonal_mul, mul_diagonal]
  exact mul_pos_iff_of_pos_right (hs j) |>.trans (mul_pos_iff_of_pos_left (inv_pos.mpr (hs i)))

/-- The complete transformations of F, T and M induced by (C.22). Γinv*J
is the inverse of the transformed lifetime matrix Jinv*Γ. -/
theorem lifetime_unit_covariance (G : Matrix m n ℝ) (S E : Matrix n m ℝ)
    (U Γinv J Jinv : Matrix m m ℝ) :
    reproductionGoods (S * J) E (Γinv * J) = reproductionGoods S E Γinv * J ∧
    (Jinv * U) * (Γinv * J) = Jinv * (U * Γinv) * J ∧
    reproductionMatrix (Jinv * G) (S * J) E (Jinv * U) (Γinv * J) =
      Jinv * reproductionMatrix G S E U Γinv * J := by
  simp [reproductionGoods, reproductionMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

end Research

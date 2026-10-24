module
public import MarxLeanProof.Productivity
public import MarxLeanProof.Units
@[expose] public section
set_option autoImplicit false

/-! # Certified truncation, Proposition 9.1
Norms in this file are the maximum absolute row-sum (infinity operator) norm.
`k` is the number of retained Neumann terms; the PDF uses k+1 terms.
-/
namespace Research
open Matrix
open scoped BigOperators Research Matrix.Norms.Operator NNReal
set_option linter.unusedSectionVars false
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- A strict positive subinvariant vector supplies the scaling required by 9.1. -/
theorem witness_scaled_norm_lt_one {A : Matrix n n ℝ} (hA : 0 ≤ A)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) (hAw : ∀ i, (A *ᵥ w) i < w i) :
    ‖inverseUnitMatrix w * A * unitMatrix w‖ < 1 := by
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup (fun i => ∑ j, ‖(inverseUnitMatrix w * A * unitMatrix w) i j‖₊) : ℝ≥0) : ℝ) < (1 : ℝ≥0)
  rw [NNReal.coe_lt_coe, Finset.sup_lt_iff (by norm_num : (0 : ℝ≥0) < 1)]
  intro i _
  rw [← NNReal.coe_lt_coe]
  simp only [NNReal.coe_sum, coe_nnnorm, inverseUnitMatrix, unitMatrix, diagonal_mul,
    mul_diagonal, Real.norm_eq_abs]
  have hn (j : n) : 0 ≤ (w i)⁻¹ * (A i j * w j) :=
    mul_nonneg (inv_nonneg.mpr (hw i).le) (mul_nonneg (hA i j) (hw j).le)
  simp only [mul_assoc]
  simp only [abs_of_nonneg (hn _), ← Finset.mul_sum]
  change (w i)⁻¹ * (A *ᵥ w) i < 1
  calc
    _ < (w i)⁻¹ * w i := mul_lt_mul_of_pos_left (hAw i) (inv_pos.mpr (hw i))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (hw i))

lemma conjugate_pow (A S T : Matrix n n ℝ) (hST : S * T = 1) (hTS : T * S = 1) (k : ℕ) :
    (T * A * S) ^ k = T * A ^ k * S := by
  induction k with
  | zero => simp [hTS]
  | succ k ih =>
    rw [pow_succ, ih, Matrix.mul_assoc T A S,
      cancel_middle (T * A ^ k) S T (A * S) hST]
    simp only [pow_succ, Matrix.mul_assoc]

lemma conjugate_partial (A S T : Matrix n n ℝ) (hST : S * T = 1) (hTS : T * S = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (T * A * S) ^ i) = T * (∑ i ∈ Finset.range k, A ^ i) * S := by
  simp only [conjugate_pow A S T hST hTS, Matrix.mul_sum, Matrix.sum_mul]

/-- Error after k Neumann terms, before a choice of units. -/
theorem labor_truncation [Nonempty n] {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (k : ℕ) (hA : ‖A‖ < 1) :
    ‖P.labor H - H * (∑ i ∈ Finset.range k, A ^ i)‖ ≤ ‖H‖ * ‖A‖ ^ k / (1 - ‖A‖) := by
  have hn : ‖P.N‖ ≤ (1 - ‖A‖)⁻¹ := by
    have hb : ‖P.N‖ ≤ 1 + ‖A‖ * ‖P.N‖ := calc
      ‖P.N‖ = ‖1 + A * P.N‖ := congrArg norm P.N_eq
      _ ≤ ‖(1 : Matrix n n ℝ)‖ + ‖A * P.N‖ := norm_add_le _ _
      _ ≤ 1 + ‖A‖ * ‖P.N‖ := by
        simpa only [norm_one] using add_le_add_right (norm_mul_le A P.N) 1
    rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hA)]
    nlinarith
  have he : P.labor H - H * (∑ i ∈ Finset.range k, A ^ i) = H * (A ^ k * P.N) := by
    unfold Productive.labor
    conv_lhs => rw [P.neumann_remainder k, Matrix.mul_add]
    abel
  rw [he]
  calc
    _ ≤ ‖H‖ * ‖A ^ k * P.N‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖H‖ * (‖A‖ ^ k * (1 - ‖A‖)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_mul_le _ _).trans
        (mul_le_mul (norm_pow_le A k) hn (norm_nonneg _) (_root_.pow_nonneg (norm_nonneg _) _))
    _ = _ := by ring

/-- The exact weighted bound in (9.2), allowing arbitrary positive diagonal S
through its two inverse equations and nonnegativity certificates. -/
theorem weighted_labor_truncation [Nonempty n] {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (S T : Matrix n n ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S * T = 1) (hTS : T * S = 1) (k : ℕ) (hA : ‖T * A * S‖ < 1) :
    ‖(P.labor H - H * (∑ i ∈ Finset.range (k + 1), A ^ i)) * S‖ ≤
      ‖H * S‖ * ‖T * A * S‖ ^ (k + 1) / (1 - ‖T * A * S‖) := by
  have h := labor_truncation (P.changeUnits S T hS hT hST hTS) (H * S) (k+1) hA
  rw [labor_change_units P H S T hS hT hST hTS,
    conjugate_partial A S T hST hTS, Matrix.mul_assoc T _ S,
    cancel_middle H S T _ hST] at h
  simpa only [Matrix.sub_mul, Matrix.mul_assoc] using h

end Research

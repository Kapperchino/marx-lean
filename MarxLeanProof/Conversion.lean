module

public import MarxLeanProof.Basic

@[expose] public section
set_option autoImplicit false

/-! # Optional labor-type conversion (PDF Appendix C)
The equal-residual condition is a predicate, never an axiom of Lean.
-/
namespace Research
open Matrix
open scoped BigOperators Research
set_option linter.unusedSectionVars false
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Reproduction goods per productive hour, C.3. -/
def reproductionGoods (S E : Matrix n m ℝ) (Γinv : Matrix m m ℝ) := S + E * Γinv

def reproductionMatrix (G : Matrix m n ℝ) (S E : Matrix n m ℝ)
    (U Γinv : Matrix m m ℝ) := G * S + (G * E + U) * Γinv

/-- Equivalence of C.2 and C.3. -/
theorem reproduction_factorization (G : Matrix m n ℝ) (S E : Matrix n m ℝ)
    (U Γinv : Matrix m m ℝ) :
    reproductionMatrix G S E U Γinv = G * reproductionGoods S E Γinv + U * Γinv := by
  simp only [reproductionMatrix, reproductionGoods, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, add_assoc]

/-- Assumption C.1, including positivity and the reference convention. -/
def EqualResidual (M : Matrix m m ℝ) (b : m) (α : m → ℝ) (κ : ℝ) : Prop :=
  (∀ i, 0 < α i) ∧ 0 < κ ∧ α b = 1 ∧ α - Mᵀ *ᵥ α = κ • (1 : m → ℝ)

namespace Conversion
variable {M : Matrix m m ℝ} (Q : Productive Mᵀ)

noncomputable def beta : m → ℝ := Q.N *ᵥ (1 : m → ℝ)
noncomputable def kappa (b : m) : ℝ := (beta Q b)⁻¹
noncomputable def alpha (b : m) : m → ℝ := kappa Q b • beta Q

lemma beta_balance : beta Q - Mᵀ *ᵥ beta Q = (1 : m → ℝ) := by
  exact sub_eq_iff_eq_add.mpr ((Q.reproduction 1).trans (add_comm _ _))

lemma beta_ge_one (i : m) : 1 ≤ beta Q i := by
  have h := congrFun (beta_balance Q) i
  have hn := mv_nonneg Q.nonneg (mv_nonneg Q.inverse_nonneg (by intro j; exact zero_le_one)) i
  change beta Q i - (Mᵀ *ᵥ beta Q) i = 1 at h
  change 0 ≤ (Mᵀ *ᵥ beta Q) i at hn
  linarith

lemma beta_pos (i : m) : 0 < beta Q i := lt_of_lt_of_le zero_lt_one (beta_ge_one Q i)
lemma kappa_pos (b : m) : 0 < kappa Q b := inv_pos.mpr (beta_pos Q b)
lemma alpha_pos (b i : m) : 0 < alpha Q b i :=
  mul_pos (kappa_pos Q b) (beta_pos Q i)

lemma alpha_reference (b : m) : alpha Q b b = 1 := by
  exact inv_mul_cancel₀ (ne_of_gt (beta_pos Q b))

/-- Theorem C.2: the displayed normalized pair satisfies every axiom. -/
theorem satisfies (b : m) : EqualResidual M b (alpha Q b) (kappa Q b) := by
  refine ⟨alpha_pos Q b, kappa_pos Q b, alpha_reference Q b, ?_⟩
  rw [alpha, mulVec_smul, ← smul_sub, beta_balance]

/-- Any solution of the linear residual equation is κβ. -/
theorem proportional {a : m → ℝ} {κ : ℝ}
    (h : a - Mᵀ *ᵥ a = κ • (1 : m → ℝ)) : a = κ • beta Q := by
  have ha : a = Mᵀ *ᵥ a + κ • (1 : m → ℝ) :=
    (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have := Q.reproduction_unique ha
  simpa only [mulVec_smul, beta] using this

/-- Theorem C.2: uniqueness includes the residual scale, not just ratios. -/
theorem unique (b : m) {a : m → ℝ} {κ : ℝ} (h : EqualResidual M b a κ) :
    a = alpha Q b ∧ κ = kappa Q b := by
  have ha := proportional Q h.2.2.2
  have hb : κ * beta Q b = 1 := by simpa only [ha, Pi.smul_apply, smul_eq_mul] using h.2.2.1
  have hk : κ = kappa Q b := by
    apply (mul_right_cancel₀ (ne_of_gt (beta_pos Q b)))
    rw [hb]
    exact (inv_mul_cancel₀ (ne_of_gt (beta_pos Q b))).symm
  exact ⟨by rw [ha, hk]; rfl, hk⟩

include Q in
theorem existsUnique (b : m) : ∃! aκ : (m → ℝ) × ℝ, EqualResidual M b aκ.1 aκ.2 := by
  refine ⟨(alpha Q b, kappa Q b), satisfies Q b, ?_⟩
  intro aκ h
  obtain ⟨ha, hk⟩ := unique Q b h
  exact Prod.ext ha hk

/-- C.6: pairwise ratios do not depend on the reference occupation. -/
theorem ratio (b i j : m) : alpha Q b i / alpha Q b j = beta Q i / beta Q j := by
  change (kappa Q b * beta Q i) / (kappa Q b * beta Q j) = _
  exact mul_div_mul_left _ _ (ne_of_gt (kappa_pos Q b))

theorem change_reference (b c i : m) : alpha Q c i = alpha Q b i / alpha Q b c := by
  rw [ratio]
  change (beta Q c)⁻¹ * beta Q i = _
  rw [div_eq_mul_inv, mul_comm]

/-- A normalized pair also supplies the strict positive-vector condition. -/
theorem witness_of_equalResidual {b : m} {a : m → ℝ} {κ : ℝ}
    (h : EqualResidual M b a κ) : ∀ i, (Mᵀ *ᵥ a) i < a i := by
  intro i
  have hi := congrFun h.2.2.2 i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hi
  linarith [h.2.1]

/-- Equal column sums give equal normalized weights, Proposition C.4. -/
theorem equal_column_sums (b : m) {s : ℝ} (hs : s < 1)
    (hM : Mᵀ *ᵥ (1 : m → ℝ) = s • (1 : m → ℝ)) : alpha Q b = 1 := by
  have h : EqualResidual M b 1 (1 - s) := by
    refine ⟨by intro i; exact zero_lt_one, sub_pos.mpr hs, rfl, ?_⟩
    rw [hM]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  exact (unique Q b h).1.symm

end Conversion

/-- A one-type reproduction coefficient ≥1 precludes a positive residual. -/
theorem no_positive_residual_scalar {μ a κ : ℝ}
    (hμ : 1 ≤ μ) (ha : 0 < a) (hκ : 0 < κ) : a - μ * a ≠ κ := by
  intro h
  nlinarith

/-- C.17: scalarizing a project adds its own labor and its input values once. -/
theorem scalar_project (G : Matrix m n ℝ) (a : n → ℝ) (h α : m → ℝ) :
    dotProduct α (h + G *ᵥ a) = dotProduct α h + dotProduct (Gᵀ *ᵥ α) a := by
  rw [dotProduct_add, dotProduct_mulVec, mulVec_transpose]

/-- C.12: exact residual-to-error identity. -/
theorem residual_error {M : Matrix m m ℝ} (Q : Productive Mᵀ) (approx : m → ℝ) :
    Conversion.beta Q - approx = Q.N *ᵥ (1 - (1 - Mᵀ) *ᵥ approx) := by
  rw [mulVec_sub, mulVec_mulVec, Q.inverse_mul, one_mulVec]
  rfl

/-- C.12: certified positive intervals give certified pairwise ratio bounds. -/
theorem ratio_bounds {li lj ui uj bi bj : ℝ}
    (hli : 0 < li) (hlj : 0 < lj) (hbi : li ≤ bi) (hbi' : bi ≤ ui)
    (hbj : lj ≤ bj) (hbj' : bj ≤ uj) : li / uj ≤ bi / bj ∧ bi / bj ≤ ui / lj := by
  constructor
  · exact div_le_div₀ (hli.le.trans hbi) hbi (hlj.trans_le hbj) hbj'
  · exact div_le_div₀ ((hli.le.trans hbi).trans hbi') hbi' hlj hbj

end Research

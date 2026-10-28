module
public import MarxLeanProof.Simulator.Analytics
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! # v6.2 §11: a certificate for the actual operator being solved -/
namespace Research.Simulator
open Matrix
open scoped BigOperators Research
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

noncomputable def weightedMax (w x : n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i| / w i)

lemma weightedMax_le {w x : n → ℝ} (hw : ∀ i, 0 < w i) {b : ℝ} :
    weightedMax w x ≤ b ↔ ∀ i, |x i| ≤ b * w i := by
  simp only [weightedMax, Finset.sup'_le_iff, Finset.mem_univ, forall_true_left,
    div_le_iff₀ (hw _)]

lemma abs_le_weightedMax {w : n → ℝ} (hw : ∀ i, 0 < w i) (x : n → ℝ) (i : n) :
    |x i| ≤ weightedMax w x * w i := (weightedMax_le hw).mp le_rfl i

lemma weightedMax_nonneg {w : n → ℝ} (hw : ∀ i, 0 < w i) (x : n → ℝ) :
    0 ≤ weightedMax w x := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have h := abs_le_weightedMax hw x i
  have h' : 0 ≤ weightedMax w x * w i := (abs_nonneg _).trans h
  exact nonneg_of_mul_nonneg_left h' (hw i)

lemma weighted_mul_bound {K : Matrix n n ℝ} (hK : 0 ≤ K)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) {c : ℝ}
    (hc : ∀ i, (K *ᵥ w) i ≤ c * w i) (x : n → ℝ) (i : n) :
    |(K *ᵥ x) i| ≤ (c * weightedMax w x) * w i := by
  calc
    _ ≤ ∑ j, |K i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, K i j * |x j| := by simp only [abs_mul, abs_of_nonneg (hK i _)]
    _ ≤ ∑ j, K i j * (weightedMax w x * w j) := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (abs_le_weightedMax hw x j) (hK i j)
    _ = weightedMax w x * (K *ᵥ w) i := by
      simp only [mulVec, dotProduct, Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ weightedMax w x * (c * w i) :=
      mul_le_mul_of_nonneg_left (hc i) (weightedMax_nonneg hw x)
    _ = _ := by ring

/-- Equation 11.3, including the coordinate scaling. No floating-point test is assumed. -/
theorem weighted_residual_bound {K : Matrix n n ℝ} (hK : 0 ≤ K)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) {c : ℝ} (hc : c < 1)
    (hKw : ∀ i, (K *ᵥ w) i ≤ c * w i)
    {b q : n → ℝ} (hq : q = b + K *ᵥ q) (approx : n → ℝ) :
    weightedMax w (q - approx) ≤ weightedMax w (b + K *ᵥ approx - approx) / (1 - c) := by
  let e := q - approx
  let r := b + K *ᵥ approx - approx
  have he : e = K *ᵥ e + r := by
    dsimp [e, r]
    rw [mulVec_sub]
    conv_lhs => rw [hq]
    abel
  have h : weightedMax w e ≤ c * weightedMax w e + weightedMax w r := by
    apply (weightedMax_le hw).mpr
    intro i
    calc
      |e i| = |(K *ᵥ e) i + r i| := congrArg (fun x : n → ℝ => |x i|) he
      _ ≤ |(K *ᵥ e) i| + |r i| := abs_add_le _ _
      _ ≤ (c * weightedMax w e) * w i + weightedMax w r * w i :=
        add_le_add (weighted_mul_bound hK hw hKw e i) (abs_le_weightedMax hw r i)
      _ = _ := by ring
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  change weightedMax w e * (1 - c) ≤ weightedMax w r
  nlinarith

/-- A positive-vector contraction certificate establishes admissibility too. -/
noncomputable def productiveOfContraction {K : Matrix n n ℝ} (hK : 0 ≤ K)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) {c : ℝ} (hc : c < 1)
    (hKw : ∀ i, (K *ᵥ w) i ≤ c * w i) : Productive K :=
  productiveOfWitness hK w hw (fun i => (hKw i).trans_lt (by nlinarith [hw i]))

/-- Equation 11.4 permits zero goods-value lower bounds. -/
theorem normalization_bounds {lo hi u blo bhi β : ℝ}
    (hlo : 0 ≤ lo) (hu : lo ≤ u) (hu' : u ≤ hi)
    (hb : 0 < blo) (hβ : blo ≤ β) (hβ' : β ≤ bhi) :
    lo / bhi ≤ u / β ∧ u / β ≤ hi / blo := by
  exact ⟨div_le_div₀ (hlo.trans hu) hu (hb.trans_le hβ) hβ',
    div_le_div₀ (hlo.trans (hu.trans hu')) hu' hb hβ⟩

end Research.Simulator

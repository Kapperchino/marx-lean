module
public import MarxLeanProof.Simulator
@[expose] public section
set_option autoImplicit false
noncomputable section

/-! # Exact v6.2 worked examples and execution counterexamples
The first group contains teaching fixtures from the PDF, never scenario defaults.
The final group contains independently chosen review regressions. Proofs use
kernel-checked arithmetic, including for rational grids; no native proof oracle.
-/
namespace Research.Simulator.Examples
open Matrix
open scoped BigOperators Research

/- §3: settled wages make the later purchase affordable. -/
theorem wage_then_purchase :
    (![10, 20, 0] : Fin 3 → ℤ) + ![6, -6, 0] + ![-12, 0, 12] = ![4, 14, 12] := by
  ext i; fin_cases i <;> norm_num

theorem purchase_needs_received_wage : ¬ (12 : ℕ) ≤ 10 ∧ 12 ≤ 10 + 6 := by decide

/- §5: A has priority but cannot fund its complete purchase. -/
def buyerA : Bundle (Fin 6) :=
  ⟨![3, 0, 0, 1, 0, 0], ![0, 0, 3, 0, 1, 0], fun _ => True⟩
def buyerB : Bundle (Fin 6) :=
  ⟨![0, 3, 0, 1, 0, 0], ![0, 0, 3, 0, 0, 1], fun _ => True⟩
def purchaseOpening : Fin 6 → ℕ := ![2, 3, 0, 1, 0, 0]

theorem failed_buyer_releases_stock :
    resolve [buyerA, buyerB] purchaseOpening = ![2, 0, 3, 0, 0, 1] := by
  have ha : ¬ buyerA.Feasible purchaseOpening := by
    simp [Bundle.Feasible, buyerA, purchaseOpening, Fin.forall_fin_succ]
  have hb : buyerB.Feasible purchaseOpening := by
    simp [Bundle.Feasible, buyerB, purchaseOpening, Fin.forall_fin_succ]
  rw [resolve_rejected buyerA _ _ ha]
  simp only [resolve, List.foldl_cons, List.foldl_nil, Bundle.commit, ite_eq_left hb]
  ext i; fin_cases i <;> norm_num [purchaseOpening, buyerB]

theorem gross_inputs_not_net_inputs :
    ¬ (Bundle.mk (fun _ : Unit => 3) (fun _ => 2) (fun _ => True)).Feasible (fun _ => 1) := by
  simp [Bundle.Feasible]

theorem cross_bank_example :
    (![12, 7, 3, 1] : Fin 4 → ℤ) + crossBankDelta 5 = ![7, 2, 8, 6] := by
  ext i; fin_cases i <;> norm_num [crossBankDelta]

/- §6: representability, binding gross inputs and retained fractional claims. -/
theorem packet_size_example : packetSize (![2, 3, 1] : Fin 3 → ℕ) = 6 := by decide

theorem packet_ticks_example :
    packetTicks (![1, 1, 1] : Fin 3 → ℕ) ![2, 3, 1] = ![3, 2, 6] := by
  ext i; fin_cases i <;> decide

theorem packet_capacity_example :
    packetCount ([0, 1] : List (Fin 2)) 4 ![8, 5] ![3, 2] = 2 := by decide

theorem packet_no_inputs : packetCount ([] : List Unit) 4 (fun _ => 0) (fun _ => 0) = 4 := rfl
theorem packet_zero_leg : packetCount [()] 4 (fun _ => 0) (fun _ => 0) = 4 := by decide

def thirds : Claim := ⟨3, by decide, 0⟩
theorem thirds_retained :
    ((thirds.accrue 1 1).accrue 1 1).numerator = 2 ∧
    (((thirds.accrue 1 1).accrue 1 1).accrue 1 1).whole = 1 := by decide

theorem fractional_settlement :
    ((Claim.mk 3 (by decide) 5).settle 1 (by decide)).numerator = 2 := by decide

/- §7: cap first on its own grid; the threshold uses floor, not cross multiplication. -/
theorem quote_below_non_grid_cap : quote (2001/1000) 0 (2009/1000) (1/100) = some 2 := by
  norm_num [quote, quoteTicks, clip]

theorem quote_empty_interval : quote 2 (2005/1000) (2009/1000) (1/100) = none := by
  norm_num [quote, quoteTicks]

theorem keyed_draw_floor_counterexample :
    drawThreshold 2 1 3 = 1 ∧ ¬ drawSuccess 2 1 3 1 ∧ 3 * (1 : ℕ) < 4 := by
  norm_num [drawSuccess, drawThreshold]

theorem smoothing_example : blend 10 14 (1/4) = 11 := by norm_num [blend]
theorem missing_observation : observedBlend 10 none (1/4) = 10 := rfl

/- §§8–11: grain, bread, coupled closure, one research attempt, residual scaling. -/
def grainA : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1; 0, 0]
def grainH : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]
def grainP : Matrix (Fin 2) (Fin 1) ℝ := !![1/8; 1/12]
def grainT : Matrix (Fin 1) (Fin 1) ℝ := !![1/4]
def grainJ : Matrix (Fin 2) (Fin 1) ℝ := !![1/2; 1]
def grainF : Matrix (Fin 1) (Fin 1) ℝ := !![2]

def grainProductive : Productive grainA where
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [grainA]
  N := !![2, 2; 0, 1]
  inverse_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  inverse_mul := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [grainA, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
    all_goals decide
  mul_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [grainA, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
    all_goals decide

theorem grain_values : (grainProductive.labor grainH)ᵀ *ᵥ ![1] = ![2, 3] := by
  ext i; fin_cases i <;>
    norm_num [Productive.labor, grainProductive, grainH, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem grain_coupled_fixed :
    coupledStep grainA grainH grainP grainT ![8, 12] ![4] = (![8, 12], ![4]) := by
  apply Prod.ext
  · change grainAᵀ *ᵥ ![8, 12] + grainHᵀ *ᵥ ![4] = ![8, 12]
    funext i
    change (grainAᵀ *ᵥ ![8, 12]) i + (grainHᵀ *ᵥ ![4]) i = ![8, 12] i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    fin_cases i <;> norm_num [grainA, grainH]
  · ext i; fin_cases i; norm_num [coupledStep, grainP, grainT, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

theorem research_attempt_six : researchValues grainJ grainF ![2, 3] ![1] = ![6] := by
  ext i; fin_cases i; norm_num [researchValues, grainJ, grainF, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem grain_gross_requirements :
    solve grainProductive (![0, 2] + grainJ *ᵥ ![1]) = ![7, 3] := by
  ext i; fin_cases i <;> norm_num [solve, grainProductive, grainJ, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]

theorem research_plan_twelve : planValue (![2, 3] : Fin 2 → ℝ) ![6] ![0, 2] ![1] = 12 := by
  norm_num [planValue, dotProduct, Fin.sum_univ_succ]

theorem research_hours_twelve : grainH *ᵥ ![7, 3] + grainF *ᵥ ![1] = ![12] := by
  ext i; fin_cases i; norm_num [grainH, grainF, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem grain_contraction : grainAᵀ *ᵥ ![1, 2] = (1/2 : ℝ) • ![1, 2] := by
  ext i; fin_cases i <;> norm_num [grainA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem grain_residual :
    (![1, 1] : Fin 2 → ℝ) + grainAᵀ *ᵥ ![19/10, 29/10] - ![19/10, 29/10] = ![1/20, 0] := by
  ext i; fin_cases i <;> norm_num [grainA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem scaled_residual_bound :
    weightedMax (![1, 2] : Fin 2 → ℝ) ![1/20, 0] / (1 - 1/2) = 1/10 := by
  norm_num [weightedMax, Fin.univ_succ, Finset.sup'_insert, Finset.sup'_singleton]

/- §§13–16: policies use exact teaching inputs, not calibration defaults. -/
theorem household_deficit :
    needDeficit (![2, 1] : Fin 2 → ℝ) ![1, 1] ![1/2, 1/2] = 1/4 := by
  norm_num [needDeficit, positivePart, Fin.sum_univ_succ]

theorem proposed_starts : proposedStarts 4 10 20 5 = 15 := by norm_num [proposedStarts, positivePart]

def exampleTax : ℚ → ℚ := incomeTax (1/10) [(100, 1/5)]

theorem wage_tax_example :
    netIncome exampleTax (1/20) 80 = 68 ∧
    netIncome exampleTax (1/20) 100 = 85 ∧
    inverseBracket 100 85 (13/20) 92 = 1440/13 ∧
    wageFloor 0 (400/13) 5 (1/100) = 154/25 ∧
    wageCap 40 (1/10) 5 (1/100) = 727/100 ∧
    netPayment exampleTax (1/20) 80 (154/5) = 1201/50 := by
  norm_num [netIncome, exampleTax, incomeTax, inverseBracket, wageFloor, ceilGrid,
    wageCap, floorGrid, netPayment]

theorem funding_prefix_example : openingNeed [8, -10] (fun _ => 0) = 8 := by
  norm_num [openingNeed, Fin.univ_succ, Finset.sup'_insert, Finset.sup'_singleton]

theorem funding_cushion_example : openingNeed [8, -10] (fun _ => 3) = 11 := by
  norm_num [openingNeed, Fin.univ_succ, Finset.sup'_insert, Finset.sup'_singleton]

theorem support_households_once : supportGrant (![2, 4, 6] : Fin 3 → ℝ) 6 = ![1, 2, 3] := by
  ext i; fin_cases i <;> norm_num [supportGrant, supportScale, Fin.sum_univ_succ]

theorem divisible_prefix_example : prefixFills 5 [2, 4, 1] = [2, 3, 0] := by
  norm_num [prefixFills, positivePart]

/- §17: indivisible jobs must use the complete resolver, not divisible prefix fills. -/
def job (amount : ℕ) : Bundle Unit := ⟨fun _ => amount, fun _ => 0, fun _ => True⟩
theorem indivisible_prefix_counterexample :
    resolve [job 6, job 4] (fun _ => 5) = fun _ => 1 := by
  have h6 : ¬ (job 6).Feasible (fun _ => 5) := by simp [job, Bundle.Feasible]
  have h4 : (job 4).Feasible (fun _ => 5) := by simp [job, Bundle.Feasible]
  rw [resolve_rejected _ _ _ h6]
  simp only [resolve, List.foldl_cons, List.foldl_nil, Bundle.commit, ite_eq_left h4]
  rfl

/- Additional review regressions; these numbers are not PDF teaching fixtures. -/
def asymmetricH : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 0, 1]
def asymmetricP : Matrix (Fin 2) (Fin 2) ℝ := !![1/4, 1/8; 0, 0]
def asymmetricT : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1/4, 0]

/-- Away from a fixed point, the second block must still read the old goods vector. -/
theorem coupled_step_old_blocks :
    coupledStep grainA asymmetricH asymmetricP asymmetricT ![2, 3] ![5, 7] =
      (![6, 19], ![13/4, 5/4]) := by
  apply Prod.ext
  · change grainAᵀ *ᵥ ![2, 3] + asymmetricHᵀ *ᵥ ![5, 7] = ![6, 19]
    funext i
    change (grainAᵀ *ᵥ ![2, 3]) i + (asymmetricHᵀ *ᵥ ![5, 7]) i = ![6, 19] i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    fin_cases i <;> norm_num [grainA, asymmetricH]
  · change (1 : Fin 2 → ℝ) + asymmetricPᵀ *ᵥ ![2, 3] +
      asymmetricTᵀ *ᵥ ![5, 7] = ![13/4, 5/4]
    funext i
    change 1 + (asymmetricPᵀ *ᵥ ![2, 3]) i +
      (asymmetricTᵀ *ᵥ ![5, 7]) i = ![13/4, 5/4] i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    fin_cases i <;> norm_num [asymmetricP, asymmetricT]

theorem unequal_occupation_fixed :
    coupledStep 0 asymmetricH asymmetricP asymmetricT ![40/23, 108/23] ![40/23, 28/23] =
      (![40/23, 108/23], ![40/23, 28/23]) := by
  apply Prod.ext
  · change (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![40/23, 108/23] +
      asymmetricHᵀ *ᵥ ![40/23, 28/23] = ![40/23, 108/23]
    rw [transpose_zero, zero_mulVec, zero_add]
    ext i; fin_cases i <;>
      norm_num [asymmetricH, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · change (1 : Fin 2 → ℝ) + asymmetricPᵀ *ᵥ ![40/23, 108/23] +
      asymmetricTᵀ *ᵥ ![40/23, 28/23] = ![40/23, 28/23]
    funext i
    change 1 + (asymmetricPᵀ *ᵥ ![40/23, 108/23]) i +
      (asymmetricTᵀ *ᵥ ![40/23, 28/23]) i = ![40/23, 28/23] i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    fin_cases i <;> norm_num [asymmetricP, asymmetricT]

theorem unequal_occupation_normalization :
    (40/23 : ℝ)⁻¹ • (![40/23, 108/23] : Fin 2 → ℝ) = ![1, 27/10] ∧
    (40/23 : ℝ)⁻¹ • (![40/23, 28/23] : Fin 2 → ℝ) = ![1, 7/10] ∧
    (40/23 : ℝ)⁻¹ = 23/40 := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    (ext i; fin_cases i <;> norm_num)

/-- §11.2: a goods-operator certificate is not a transpose-operator certificate. -/
theorem certificate_does_not_transfer_to_transpose :
    grainA *ᵥ ![3, 1] ≤ (5/6 : ℝ) • ![3, 1] ∧
    ¬ grainAᵀ *ᵥ ![3, 1] ≤ (5/6 : ℝ) • ![3, 1] := by
  norm_num [Pi.le_def, Fin.forall_fin_succ, grainA, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The goods account still exists when the optional reproduction closure fails. -/
theorem optional_closure_can_fail :
    (zeroProductive.labor (!![1] : Matrix (Fin 1) (Fin 1) ℝ))ᵀ *ᵥ ![1] = ![1] ∧
    ¬ Nonempty (Productive (coupledOperator (0 : Matrix (Fin 1) (Fin 1) ℝ)
      !![1] !![1] 0)) := by
  constructor
  · ext i; fin_cases i
    norm_num [Productive.labor, zeroProductive, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_succ]
  · rintro ⟨C⟩
    obtain ⟨w, _, hw⟩ := C.positive_witness
    have hg := hw (Sum.inl 0)
    have ho := hw (Sum.inr 0)
    simp only [coupledOperator, fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr,
      transpose_zero, zero_mulVec, zero_add, add_zero] at hg ho
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hg ho
    linarith

end Research.Simulator.Examples

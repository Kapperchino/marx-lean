module
public import Mathlib
@[expose] public section
set_option autoImplicit false

/-! # v6.2 §§7,13–16: policy formulas and their mathematical domains
These are proposals evaluated from admitted observations. They do not post
payments, allocate resources or confer consent. Real curves below are the
mathematical specification, not the GPU-D1 integer-table implementation.
-/
noncomputable section
namespace Research.Simulator
open scoped BigOperators

def positivePart (x : ℝ) : ℝ := max 0 x
def clip {α : Type*} [LinearOrder α] (x lo hi : α) : α := min hi (max lo x)

theorem clip_bounds {α : Type*} [LinearOrder α] (x : α) {lo hi : α} (h : lo ≤ hi) :
    lo ≤ clip x lo hi ∧ clip x lo hi ≤ hi :=
  ⟨le_min h (le_max_left _ _), min_le_left _ _⟩

def blend (x y weight : ℝ) : ℝ := x + weight * (y - x)

theorem blend_convex (x y weight : ℝ) :
    blend x y weight = (1 - weight) * x + weight * y := by unfold blend; ring

def observedBlend (old : ℝ) (signal : Option ℝ) (weight : ℝ) : ℝ :=
  signal.elim old (fun x => blend old x weight)

/-- Equation 7.2. Rational arithmetic makes both grid endpoints exact. -/
def quoteTicks (candidate lo hi quantum : ℚ) : Option ℤ :=
  if 0 < quantum ∧ Int.ceil (lo / quantum) ≤ Int.floor (hi / quantum) then
    some (clip (Int.ceil (candidate / quantum)) (Int.ceil (lo / quantum))
      (Int.floor (hi / quantum)))
  else none

def quote (candidate lo hi quantum : ℚ) : Option ℚ :=
  (quoteTicks candidate lo hi quantum).map (fun ticks => quantum * ticks)

theorem quoteTicks_bounds {candidate lo hi quantum : ℚ} {ticks : ℤ}
    (h : quoteTicks candidate lo hi quantum = some ticks) :
    0 < quantum ∧ Int.ceil (lo / quantum) ≤ ticks ∧ ticks ≤ Int.floor (hi / quantum) := by
  unfold quoteTicks at h
  split_ifs at h with hok
  · cases h
    exact ⟨hok.1, clip_bounds _ hok.2⟩

theorem quoteTicks_legal {candidate lo hi quantum : ℚ} {ticks : ℤ}
    (h : quoteTicks candidate lo hi quantum = some ticks) :
    lo ≤ quantum * ticks ∧ quantum * ticks ≤ hi := by
  obtain ⟨hq, hl, hu⟩ := quoteTicks_bounds h
  have hl' : lo / quantum ≤ (ticks : ℚ) :=
    (Int.le_ceil _).trans (by exact_mod_cast hl)
  have hu' : (ticks : ℚ) ≤ hi / quantum :=
    (show (ticks : ℚ) ≤ (Int.floor (hi / quantum) : ℚ) by exact_mod_cast hu).trans
      (Int.floor_le _)
  constructor
  · simpa [mul_comm] using (div_le_iff₀ hq).mp hl'
  · simpa [mul_comm] using (le_div_iff₀ hq).mp hu'

noncomputable def hazard (exposure : ℝ) : ℝ := 1 - Real.exp (-exposure)
noncomputable def sigmoid (score : ℝ) : ℝ := 1 / (1 + Real.exp (-score))

theorem hazard_zero : hazard 0 = 0 := by simp [hazard]

theorem hazard_bounds {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hazard x ∧ hazard x < 1 := by
  have he : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
  have hp := Real.exp_pos (-x)
  constructor <;> dsimp [hazard] <;> linarith

/-- S9.1, with an explicit zero-need branch. -/
noncomputable def needDeficit {service : Type*} [Fintype service]
    (need delivered weight : service → ℝ) : ℝ :=
  ∑ i, if 0 < need i then weight i * (positivePart (need i - delivered i) / need i) else 0

theorem needDeficit_bounds {service : Type*} [Fintype service]
    (need delivered weight : service → ℝ)
    (hs : ∀ i, 0 ≤ delivered i) (hw : ∀ i, 0 ≤ weight i)
    (ht : (∑ i, if 0 < need i then weight i else 0) ≤ 1) :
    0 ≤ needDeficit need delivered weight ∧ needDeficit need delivered weight ≤ 1 := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs with hn
    · exact mul_nonneg (hw i) (div_nonneg (le_max_left _ _) hn.le)
    · exact le_rfl
  · apply le_trans (Finset.sum_le_sum (g := fun i => if 0 < need i then weight i else 0) ?_) ht
    intro i _
    split_ifs with hn
    · have hratio : positivePart (need i - delivered i) / need i ≤ 1 := by
        apply (div_le_one hn).mpr
        exact max_le hn.le (sub_le_self _ (hs i))
      simpa using mul_le_mul_of_nonneg_left hratio (hw i)
    · exact le_rfl

/-- S9.2: one shared clock. `reserved` sums rest/care/education/travel/organization. -/
def availableHours (participates : Bool) (cap health fatigue reserved : ℝ) : ℝ :=
  if participates then min (cap * health * (1 - fatigue)) (positivePart (24 - reserved)) else 0

def nextHealth (health fatigue deficit recovery damage fatigueDamage : ℝ) : ℝ :=
  clip (health + recovery * (1 - health) * (1 - deficit) - damage * deficit -
    fatigueDamage * fatigue) 0 1

def nextFatigue (fatigue response exertion rest : ℝ) : ℝ :=
  clip (fatigue + response * ((exertion - rest) / 8)) 0 1

def forecast (old sales validUnfilled weight : ℝ) : ℝ := blend old (sales + validUnfilled) weight
def proposedStarts (coverage demand finished pipeline : ℝ) : ℝ :=
  positivePart (coverage * demand - (finished + pipeline))

def machineServiceCap (remaining condition nameplate downtime : ℝ) : ℝ :=
  min remaining (condition * (nameplate - downtime))

/-- Maintenance repairs condition but cannot replenish lifetime service (S9.6). -/
def nextMachine (remaining condition used wear restoration maintenance : ℝ) : ℝ × ℝ :=
  (remaining - used, clip (condition - wear * used + restoration * maintenance) 0 1)

theorem machine_lifetime_nonincreasing (remaining condition used wear restoration maintenance : ℝ)
    (hu : 0 ≤ used) : (nextMachine remaining condition used wear restoration maintenance).1 ≤ remaining :=
  sub_le_self _ hu

def renewableStock (stock extraction capacity rate : ℝ) : ℝ :=
  let remaining := stock - extraction
  remaining * (1 + rate * (1 - remaining / capacity))

theorem renewableStock_bounds {stock extraction capacity rate : ℝ}
    (hu : 0 ≤ extraction) (hus : extraction ≤ stock) (hs : stock ≤ capacity)
    (hk : 0 < capacity) (hr : 0 ≤ rate) (hr' : rate ≤ 1) :
    0 ≤ renewableStock stock extraction capacity rate ∧
      renewableStock stock extraction capacity rate ≤ capacity := by
  have hrem : 0 ≤ stock - extraction := sub_nonneg.mpr hus
  have hrem' : stock - extraction ≤ capacity := by linarith
  have hfrac : 0 ≤ 1 - (stock - extraction) / capacity := by
    linarith [(div_le_one hk).mpr hrem']
  have he : rate * (1 - (stock - extraction) / capacity) ≤
      1 - (stock - extraction) / capacity := by
    simpa using mul_le_mul_of_nonneg_right hr' hfrac
  constructor
  · exact mul_nonneg hrem (by nlinarith [mul_nonneg hr hfrac])
  · unfold renewableStock
    have hm := mul_le_mul_of_nonneg_left he hrem
    have hdiv : (stock - extraction) / capacity * capacity = stock - extraction :=
      div_mul_cancel₀ _ (ne_of_gt hk)
    have hsquare := sq_nonneg (capacity - (stock - extraction))
    nlinarith

/-- S9.8 before the separate legal grid projection. `unitGood` carries output units. -/
noncomputable def priceCandidate (price response unfilled excess demand unitGood : ℝ) : ℝ :=
  price * Real.exp (response * clip ((unfilled - excess) / max demand unitGood) (-1) 1)

noncomputable def researchScale (minimum pioneer exposure capacity relatedness shape : ℝ) : ℝ :=
  blend minimum pioneer ((1 - exposure * capacity * relatedness) ^ shape)

noncomputable def researchSuccess (effort scale : ℝ) : ℝ := hazard (effort / scale)
noncomputable def nextExposure (exposure signal : ℝ) : ℝ := blend exposure 1 (hazard signal)

theorem researchSuccess_zero (scale : ℝ) : researchSuccess 0 scale = 0 := by
  simp [researchSuccess, hazard_zero]

/-- S10.1: each pair is (threshold, change in marginal rate). -/
def incomeTax (baseRate : ℚ) (brackets : List (ℚ × ℚ)) (income : ℚ) : ℚ :=
  baseRate * income + (brackets.map (fun b => b.2 * max 0 (income - b.1))).sum

def netIncome (tax : ℚ → ℚ) (employeeCharge income : ℚ) : ℚ :=
  (1 - employeeCharge) * income - tax income

def netPayment (tax : ℚ → ℚ) (employeeCharge prior gross : ℚ) : ℚ :=
  netIncome tax employeeCharge (prior + gross) - netIncome tax employeeCharge prior

/-- Paid-income increments telescope across employers rather than restarting allowances. -/
theorem netPayment_telescope (tax : ℚ → ℚ) (charge prior first second : ℚ) :
    netPayment tax charge prior first + netPayment tax charge (prior + first) second =
      netPayment tax charge prior (first + second) := by
  simp only [netPayment, add_assoc]; ring

/-- Withholding partitions gross pay instead of charging it twice. -/
theorem payroll_partition (tax : ℚ → ℚ) (charge prior gross : ℚ) :
    netPayment tax charge prior gross + (tax (prior + gross) - tax prior) +
      charge * gross = gross := by
  unfold netPayment netIncome
  ring

def inverseBracket (threshold netAtThreshold slope target : ℚ) : ℚ :=
  threshold + (target - netAtThreshold) / slope

theorem inverseBracket_correct (threshold netAtThreshold slope target : ℚ) (h : slope ≠ 0) :
    netAtThreshold + slope * (inverseBracket threshold netAtThreshold slope target - threshold) = target := by
  unfold inverseBracket; field_simp; ring

def ceilGrid (x quantum : ℚ) : ℚ := quantum * Int.ceil (x / quantum)
def floorGrid (x quantum : ℚ) : ℚ := quantum * Int.floor (x / quantum)
def wageFloor (legal grossNeeded payableHours quantum : ℚ) : ℚ :=
  ceilGrid (max legal (grossNeeded / payableHours)) quantum
def wageCap (funded employerCharge payableHours quantum : ℚ) : ℚ :=
  floorGrid (funded / ((1 + employerCharge) * payableHours)) quantum
def payrollCeiling (receipts nonlabor contingency budget : ℝ) : ℝ :=
  clip (receipts - nonlabor - contingency) 0 budget

def householdAnchor (cashCost fundedOther adults normalDay : ℝ) : ℝ :=
  positivePart (cashCost - fundedOther) / (adults * normalDay)
def refusalFactor (coverDays : ℝ) : ℝ := 3 / 5 + (2 / 35) * min coverDays (21 / 2)
def requiredNetRate (cashCost coverDays anchor workCost : ℝ) : ℝ :=
  (if cashCost = 0 then 6 / 5 else refusalFactor coverDays) * anchor + workCost

theorem refusalFactor_bounds {cover : ℝ} (h : 0 ≤ cover) :
    3 / 5 ≤ refusalFactor cover ∧ refusalFactor cover ≤ 6 / 5 := by
  have hlo : 0 ≤ min cover (21 / 2 : ℝ) := le_min h (by norm_num)
  have hhi := min_le_right cover (21 / 2 : ℝ)
  unfold refusalFactor; constructor <;> linarith

def bargainingWeight (mandate withdrawal alternatives concentration replacements : ℝ) : ℝ :=
  max 1 (7 + 5 * mandate + 4 * withdrawal + 3 * alternatives -
    4 * concentration - 3 * replacements) / 20

def secondOffer (first desired weight lo hi quantum : ℚ) : ℚ :=
  clip (floorGrid (first + weight * (desired - first)) quantum) lo hi

def strikeScore (grievance solidarity trust efficacy peers cost risk : ℝ) : ℝ :=
  2 * grievance + solidarity + trust + efficacy + peers - 2 * cost - risk - 3 / 2

theorem strikeScore_bounds {g s u e n c r : ℝ}
    (hg : g ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) (hu : u ∈ Set.Icc 0 1)
    (he : e ∈ Set.Icc 0 1) (hn : n ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (hr : r ∈ Set.Icc 0 1) : strikeScore g s u e n c r ∈ Set.Icc (-(9 / 2)) (9 / 2) := by
  rcases hg with ⟨hg, hg'⟩; rcases hs with ⟨hs, hs'⟩; rcases hu with ⟨hu, hu'⟩
  rcases he with ⟨he, he'⟩; rcases hn with ⟨hn, hn'⟩; rcases hc with ⟨hc, hc'⟩
  rcases hr with ⟨hr, hr'⟩
  constructor <;> dsimp [strikeScore] <;> linarith

end Research.Simulator

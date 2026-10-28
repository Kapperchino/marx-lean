module
public import MarxLeanProof.Simulator.Policies
@[expose] public section
set_option autoImplicit false

/-! # v6.2 §16: lending, dated funding and household support -/
noncomputable section
namespace Research.Simulator
open scoped BigOperators

/-- S11.1. Domain: term, capital ratio and risk weight positive; rate and
liquidity nonnegative. Caps affect new lending, never existing balances. -/
def lendingLimit (requested term rate surplus debtService serviceFraction
    advance collateral secured equity minCapital riskAssets riskWeight liquidity : ℝ) : ℝ :=
  positivePart (min requested (min (term * (serviceFraction * surplus - debtService) /
    (1 + rate * term)) (min (advance * collateral - secured)
      (min ((equity - minCapital * riskAssets) / (minCapital * riskWeight)) liquidity))))

theorem lendingLimit_liquidity (requested term rate surplus debtService serviceFraction
    advance collateral secured equity minCapital riskAssets riskWeight liquidity : ℝ)
    (hl : 0 ≤ liquidity) :
    lendingLimit requested term rate surplus debtService serviceFraction advance collateral
      secured equity minCapital riskAssets riskWeight liquidity ≤ liquidity := by
  apply max_le hl
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))

/-- S11.2 includes prefix zero, and `costs` are outflows minus receipts in order. -/
def openingNeed (costs : List ℝ) (cushion : Fin (costs.length + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k => cushion k + (costs.take k.val).sum)

def financingGap (required openingCash : ℝ) : ℝ := positivePart (required - openingCash)

/-- The maximum prefix shortage is exactly the condition for every cushion. -/
theorem openingNeed_iff (costs : List ℝ) (cushion : Fin (costs.length + 1) → ℝ)
    (cash : ℝ) : openingNeed costs cushion ≤ cash ↔
      ∀ k, cushion k ≤ cash - (costs.take k.val).sum := by
  simp only [openingNeed, Finset.sup'_le_iff, Finset.mem_univ, forall_true_left]
  exact forall_congr' fun k => by constructor <;> intro h <;> linarith

def replacementEarmark (target earmarked freeCash : ℝ) : ℝ :=
  clip (target - earmarked) 0 freeCash
def rentBid (fraction beforeRent retained budget : ℝ) : ℝ :=
  fraction * clip (beforeRent - retained) 0 budget
def discountWeight (dailyRate : ℝ) (days : ℕ) : ℝ := ((1 + dailyRate) ^ days)⁻¹
def discountedFlows (dailyRate : ℝ) (flows : List ℝ) : ℝ :=
  ((flows.zipIdx).map fun p => discountWeight dailyRate p.2 * p.1).sum

def supportScale (total treasury : ℝ) : ℝ :=
  if total = 0 then 0 else min 1 (treasury / total)

def supportGrant {household : Type*} [Fintype household]
    (need : household → ℝ) (treasury : ℝ) (h : household) : ℝ :=
  supportScale (∑ j, need j) treasury * need h

theorem supportScale_bounds {total treasury : ℝ} (ht : 0 ≤ total) (hf : 0 ≤ treasury) :
    0 ≤ supportScale total treasury ∧ supportScale total treasury ≤ 1 := by
  unfold supportScale
  split_ifs
  · norm_num
  · exact ⟨le_min zero_le_one (div_nonneg hf ht), min_le_left _ _⟩

/-- Each household is indexed once. Eligibility and confirmations precede posting. -/
theorem supportGrant_bounds {household : Type*} [Fintype household]
    (need : household → ℝ) (treasury : ℝ) (hn : ∀ h, 0 ≤ need h) (hf : 0 ≤ treasury)
    (h : household) : 0 ≤ supportGrant need treasury h ∧ supportGrant need treasury h ≤ need h := by
  obtain ⟨hl, hu⟩ := supportScale_bounds (Finset.sum_nonneg (fun j _ => hn j)) hf
  exact ⟨mul_nonneg hl (hn h), by simpa [supportGrant] using mul_le_mul_of_nonneg_right hu (hn h)⟩

theorem supportGrant_total {household : Type*} [Fintype household]
    (need : household → ℝ) (treasury : ℝ) (hn : ∀ h, 0 ≤ need h) (hf : 0 ≤ treasury) :
    ∑ h, supportGrant need treasury h = min treasury (∑ h, need h) := by
  simp only [supportGrant, ← Finset.mul_sum]
  have hsum : 0 ≤ ∑ h, need h := Finset.sum_nonneg fun j _ => hn j
  unfold supportScale
  split_ifs with hz
  · simp [hz, min_eq_right hf]
  · have hp : 0 < ∑ h, need h := lt_of_le_of_ne hsum (Ne.symm hz)
    by_cases hle : treasury ≤ ∑ h, need h
    · rw [min_eq_right ((div_le_one hp).mpr hle), min_eq_left hle,
        div_mul_cancel₀ _ hz]
    · have hge := le_of_not_ge hle
      rw [min_eq_left ((one_le_div hp).mpr hge), min_eq_right hge, one_mul]

/-- S17.1 is defined only as a divisible-pool allocation, with no inflows or
private failure gates. The residual update below has the serial partial-fill meaning. -/
def prefixFills (capacity : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: rest => min a (positivePart capacity) :: prefixFills (positivePart (capacity - a)) rest

theorem partialFill_remaining {capacity demand : ℝ} (_hc : 0 ≤ capacity) (_hd : 0 ≤ demand) :
    capacity - min demand capacity = positivePart (capacity - demand) := by
  unfold positivePart
  by_cases h : demand ≤ capacity
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem prefixFills_total (capacity : ℝ) (demands : List ℝ)
    (hc : 0 ≤ capacity) (hd : ∀ a ∈ demands, 0 ≤ a) :
    (prefixFills capacity demands).sum = min capacity demands.sum := by
  induction demands generalizing capacity with
  | nil => simp [prefixFills, min_eq_right hc]
  | cons a rest ih =>
    have ha := hd a (by simp)
    have hr : ∀ b ∈ rest, 0 ≤ b := fun b hb => hd b (by simp [hb])
    have hs : 0 ≤ rest.sum := List.sum_nonneg hr
    simp only [prefixFills, List.sum_cons]
    rw [ih (positivePart (capacity - a)) (le_max_left _ _) hr]
    rw [show positivePart capacity = capacity from max_eq_right hc]
    rw [← partialFill_remaining hc ha]
    by_cases hac : a ≤ capacity
    · rw [min_eq_left hac]
      by_cases h : rest.sum ≤ capacity - a
      · rw [min_eq_right h, min_eq_right (by linarith)]
      · rw [min_eq_left (le_of_not_ge h), min_eq_left (by linarith)]; ring
    · rw [min_eq_right (le_of_not_ge hac)]
      rw [sub_self, min_eq_left hs, min_eq_left (by linarith)]
      ring

end Research.Simulator

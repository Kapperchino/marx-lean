module
public import MarxLeanProof.Simulator.Ledger
@[expose] public section
set_option autoImplicit false

/-! # v6.2 §6.1: the exact activity lattice and gross resource bounds -/
namespace Research.Simulator
variable {leg resource : Type*} [Fintype leg]

/-- Denominators refer to reduced ticks-per-activity fractions. -/
def packetSize (denominator : leg → ℕ) : ℕ := Finset.univ.lcm denominator

theorem denominator_dvd_packet (denominator : leg → ℕ) (i : leg) :
    denominator i ∣ packetSize denominator := Finset.dvd_lcm (Finset.mem_univ i)

theorem packetSize_pos {denominator : leg → ℕ} (h : ∀ i, 0 < denominator i) :
    0 < packetSize denominator := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun i _ => Nat.ne_of_gt (h i))

theorem packetSize_minimal (denominator : leg → ℕ) (candidate : ℕ) :
    packetSize denominator ∣ candidate ↔ ∀ i, denominator i ∣ candidate := by
  simp [packetSize, Finset.lcm_dvd_iff]

def packetTicks (numerator denominator : leg → ℕ) (i : leg) : ℕ :=
  (packetSize denominator / denominator i) * numerator i

/-- Multiplying through by the denominator proves exact representability. -/
theorem packetTicks_exact (numerator denominator : leg → ℕ) (i : leg) :
    packetTicks numerator denominator i * denominator i =
      packetSize denominator * numerator i := by
  unfold packetTicks
  rw [Nat.mul_right_comm, Nat.div_mul_cancel (denominator_dvd_packet denominator i)]

/-- Zero-input legs impose no bound; an empty list leaves the plan unchanged.
The list must cover all consumed resources before using the result as a bound. -/
def packetCount (resources : List resource) (plan : ℕ)
    (available debit : resource → ℕ) : ℕ :=
  resources.foldr (fun i q => if debit i = 0 then q else min q (available i / debit i)) plan

/-- Equation 6.3 is the greatest feasible count for exclusively assigned resources. -/
theorem le_packetCount_iff (resources : List resource) (plan q : ℕ)
    (available debit : resource → ℕ) :
    q ≤ packetCount resources plan available debit ↔
      q ≤ plan ∧ ∀ i ∈ resources, q * debit i ≤ available i := by
  induction resources with
  | nil => simp [packetCount]
  | cons i rest ih =>
    simp only [packetCount, List.foldr_cons]
    by_cases hd : debit i = 0
    · simp only [hd, ite_true]
      simpa [packetCount, hd] using ih
    · rw [ite_eq_right hd, le_min_iff]
      change (q ≤ packetCount rest plan available debit ∧ q ≤ available i / debit i) ↔ _
      rw [ih, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd)]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

theorem packetCount_feasible (resources : List resource) (plan : ℕ)
    (available debit : resource → ℕ) :
    packetCount resources plan available debit ≤ plan ∧
      ∀ i ∈ resources, packetCount resources plan available debit * debit i ≤ available i :=
  (le_packetCount_iff resources plan _ available debit).mp le_rfl

end Research.Simulator

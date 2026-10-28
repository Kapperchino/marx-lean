module
public import Mathlib
@[expose] public section
set_option autoImplicit false

/-! # v6.2 §§5–6: exact ticks, complete commitments and fractional claims
Integers are unbounded mathematical integers. Hardware range checks are a
separate implementation obligation. Resource indices identify owner, instrument,
unit and attributes; aggregation across unlike instruments is not assumed.
-/
namespace Research.Simulator
open scoped BigOperators

structure Coordinate (owner instrument unit attributes : Type*) where
  holder : owner
  asset : instrument
  denomination : unit
  locationQuality : attributes
  deriving DecidableEq

structure Quantum where
  size : ℚ
  positive : 0 < size

def physicalAmount (unit : Quantum) (ticks : ℤ) : ℚ := unit.size * ticks

/-- Equation 5.2, applicable to signed accounting coordinates as well as stocks. -/
def post {r e : Type*} (s : r → ℤ) (delta : e → r → ℤ) (accepted : Finset e) : r → ℤ :=
  fun i => s i + ∑ event ∈ accepted, delta event i

theorem post_conserves {r e : Type*} [Fintype r]
    (s : r → ℤ) (delta : e → r → ℤ) (accepted : Finset e)
    (balanced : ∀ event ∈ accepted, ∑ i, delta event i = 0) :
    ∑ i, post s delta accepted i = ∑ i, s i := by
  simp only [post, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have hz : ∑ event ∈ accepted, ∑ i, delta event i = 0 :=
    Finset.sum_eq_zero balanced
  rw [hz, add_zero]

/-- Gross debits are grouped per coordinate. `authorized` includes contract,
consent, access, version, timing and other gates supplied by the scenario. -/
structure Bundle (r : Type*) where
  debit : r → ℕ
  credit : r → ℕ
  authorized : (r → ℕ) → Prop

def Bundle.Feasible {r : Type*} (e : Bundle r) (s : r → ℕ) : Prop :=
  e.authorized s ∧ ∀ i, e.debit i ≤ s i

/-- Acceptance posts every leg. Subtraction is used only after the gross check. -/
noncomputable def Bundle.commit {r : Type*} (e : Bundle r) (s : r → ℕ) : r → ℕ := by
  classical
  exact if e.Feasible s then fun i => s i - e.debit i + e.credit i else s

theorem Bundle.rejected {r : Type*} (e : Bundle r) (s : r → ℕ)
    (h : ¬ e.Feasible s) : e.commit s = s := by simp [Bundle.commit, h]

theorem Bundle.accepted {r : Type*} (e : Bundle r) (s : r → ℕ)
    (h : e.Feasible s) (i : r) :
    (e.commit s i : ℤ) = (s i : ℤ) - e.debit i + e.credit i := by
  simp [Bundle.commit, h, Int.ofNat_sub (h.2 i)]

noncomputable def resolve {r : Type*} (events : List (Bundle r)) (s : r → ℕ) : r → ℕ :=
  events.foldl (fun state event => event.commit state) s

/-- A rejected predecessor leaves resources available to its successor. -/
theorem resolve_rejected {r : Type*} (e : Bundle r) (events : List (Bundle r))
    (s : r → ℕ) (h : ¬ e.Feasible s) : resolve (e :: events) s = resolve events s := by
  simp [resolve, e.rejected s h]

/-- Four distinct roles in a cross-bank payment (5.3). Same-bank payments
instead use only the two customer deposit legs. -/
def crossBankDelta (amount : ℤ) : Fin 4 → ℤ := ![-amount, -amount, amount, amount]

theorem crossBank_deposits (s : Fin 4 → ℤ) (amount : ℤ) :
    (s 0 + crossBankDelta amount 0) + (s 3 + crossBankDelta amount 3) = s 0 + s 3 := by
  simp [crossBankDelta]; ring

theorem crossBank_reserves (s : Fin 4 → ℤ) (amount : ℤ) :
    (s 1 + crossBankDelta amount 1) + (s 2 + crossBankDelta amount 2) = s 1 + s 2 := by
  simp [crossBankDelta]; ring

/-- One fixed-denominator tranche, with counterparties/currency supplied by its key. -/
structure Claim where
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator : ℕ

def Claim.whole (c : Claim) : ℕ := c.numerator / c.denominator
def Claim.remainder (c : Claim) : ℕ := c.numerator % c.denominator
def Claim.accrue (c : Claim) (rate units : ℕ) : Claim :=
  { c with numerator := c.numerator + rate * units }

/-- Cash funding and permission are checked by the associated payment bundle.
This transition updates only the claim, after a permitted cash settlement. -/
def Claim.settle (c : Claim) (paid : ℕ) (_h : paid ≤ c.whole) : Claim :=
  { c with numerator := c.numerator - c.denominator * paid }

theorem Claim.decompose (c : Claim) :
    c.numerator = c.denominator * c.whole + c.remainder := by
  simpa [Claim.whole, Claim.remainder, Nat.mul_comm] using
    (Nat.div_add_mod' c.numerator c.denominator).symm

theorem Claim.remainder_lt (c : Claim) : c.remainder < c.denominator :=
  Nat.mod_lt _ c.denominator_pos

theorem Claim.settle_conserves (c : Claim) (paid : ℕ) (h : paid ≤ c.whole) :
    (c.settle paid h).numerator + c.denominator * paid = c.numerator := by
  apply Nat.sub_add_cancel
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le c.denominator_pos).mp h

theorem Claim.settle_remainder (c : Claim) (paid : ℕ) (h : paid ≤ c.whole) :
    (c.settle paid h).remainder = c.remainder := by
  have hc := c.settle_conserves paid h
  have hm := congrArg (fun n => n % c.denominator) hc
  simpa [Claim.remainder, Claim.settle, Nat.add_mod] using hm

end Research.Simulator

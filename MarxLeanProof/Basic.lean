module

public import Mathlib

@[expose] public section
set_option autoImplicit false

/-!
# Productive production systems (PDF §§2–3)

`Productive A` packages the *nonnegative two-sided inverse* criterion (iii) of
Theorem 3.1. It does not assume any labor-account conclusion. All coefficients
are real, indices are finite, and inequalities are entrywise.
-/

set_option linter.unusedSectionVars false

namespace Research
open Matrix
/-- Entrywise order, deliberately distinct from Mathlib's positive-semidefinite order. -/
scoped instance {i j : Type*} : PartialOrder (Matrix i j ℝ) :=
  inferInstanceAs (PartialOrder (i → j → ℝ))
scoped instance {i j : Type*} : IsOrderedAddMonoid (Matrix i j ℝ) :=
  inferInstanceAs (IsOrderedAddMonoid (i → j → ℝ))
open scoped BigOperators Research

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq m] [DecidableEq p]

lemma mm_nonneg {A : Matrix m n ℝ} {B : Matrix n p ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A * B := by
  intro i j
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

lemma mv_nonneg {A : Matrix m n ℝ} {x : n → ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := by
  intro i
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

lemma mm_mono {A A' : Matrix m n ℝ} {B B' : Matrix n p ℝ}
    (hA : 0 ≤ A) (hB' : 0 ≤ B') (hAA : A ≤ A') (hBB : B ≤ B') :
    A * B ≤ A' * B' := by
  intro i j
  apply Finset.sum_le_sum
  intro k _
  exact (mul_le_mul_of_nonneg_left (hBB k j) (hA i k)).trans
    (mul_le_mul_of_nonneg_right (hAA i k) (hB' k j))

lemma mv_mono {A : Matrix m n ℝ} {x y : n → ℝ}
    (hA : 0 ≤ A) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := by
  intro i
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hA i j)

/-- A checkable form of the productive-inverse criterion, PDF Theorem 3.1(iii). -/
structure Productive (A : Matrix n n ℝ) where
  nonneg : 0 ≤ A
  N : Matrix n n ℝ
  inverse_nonneg : 0 ≤ N
  inverse_mul : N * (1 - A) = 1
  mul_inverse : (1 - A) * N = 1

namespace Productive
variable {A : Matrix n n ℝ} (P : Productive A)
include P

lemma inverse_eq : P.N = (1 - A)⁻¹ := by
  exact Matrix.inv_eq_left_inv P.inverse_mul |>.symm

lemma N_eq : P.N = 1 + A * P.N := by
  have h := P.mul_inverse
  rw [Matrix.sub_mul, Matrix.one_mul] at h
  exact sub_eq_iff_eq_add.mp h

lemma N_eq' : P.N = 1 + P.N * A := by
  have h := P.inverse_mul
  rw [Matrix.mul_sub, Matrix.mul_one] at h
  exact sub_eq_iff_eq_add.mp h

lemma one_le_N : 1 ≤ P.N := by
  rw [P.N_eq]
  exact le_add_of_nonneg_right (mm_nonneg P.nonneg P.inverse_nonneg)

/-- Theorem 3.1(v), with uniqueness even among signed solutions. -/
theorem reproduction (y : n → ℝ) :
    P.N *ᵥ y = A *ᵥ (P.N *ᵥ y) + y := by
  have h : (1 - A) *ᵥ (P.N *ᵥ y) = y := by
    rw [mulVec_mulVec, P.mul_inverse, one_mulVec]
  rw [sub_mulVec, one_mulVec] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

theorem reproduction_unique {y x : n → ℝ} (hx : x = A *ᵥ x + y) :
    x = P.N *ᵥ y := by
  have h : (1 - A) *ᵥ x = y := by rw [sub_mulVec, one_mulVec]; exact sub_eq_iff_eq_add.mpr (hx.trans (add_comm _ _))
  rw [← h, mulVec_mulVec, P.inverse_mul, one_mulVec]

theorem reproduction_existsUnique {y : n → ℝ} (hy : 0 ≤ y) :
    ∃! x : n → ℝ, 0 ≤ x ∧ x = A *ᵥ x + y := by
  exact ⟨P.N *ᵥ y, ⟨mv_nonneg P.inverse_nonneg hy, P.reproduction y⟩,
    fun _ h => P.reproduction_unique h.2⟩

/-- The positive-vector certificate in Theorem 3.1(iv). -/
theorem positive_witness :
    ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ ∀ i, (A *ᵥ w) i < w i := by
  let w := P.N *ᵥ (1 : n → ℝ)
  have hw := P.reproduction (1 : n → ℝ)
  have hn := mv_nonneg P.nonneg (mv_nonneg P.inverse_nonneg (by intro i; exact zero_le_one))
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hi := congrFun hw i
    have hi' := hn i
    change w i = (A *ᵥ w) i + 1 at hi
    change 0 ≤ (A *ᵥ w) i at hi'
    linarith
  · intro i
    have hi := congrFun hw i
    change w i = (A *ᵥ w) i + 1 at hi
    linarith

/-- The occupational labor account. -/
def labor (H : Matrix m n ℝ) : Matrix m n ℝ := H * P.N

lemma labor_nonneg {H : Matrix m n ℝ} (hH : 0 ≤ H) : 0 ≤ P.labor H :=
  mm_nonneg hH P.inverse_nonneg

lemma labor_balance (H : Matrix m n ℝ) : P.labor H * (1 - A) = H := by
  simp only [labor, Matrix.mul_assoc, P.inverse_mul, Matrix.mul_one]

/-- Theorem 3.2, fixed-point identity. -/
theorem labor_fixed (H : Matrix m n ℝ) : P.labor H = H + P.labor H * A := by
  have h := P.labor_balance H
  rw [Matrix.mul_sub, Matrix.mul_one] at h
  exact sub_eq_iff_eq_add.mp h

/-- Theorem 3.2, uniqueness. -/
theorem labor_unique {H G : Matrix m n ℝ} (hG : G = H + G * A) : G = P.labor H := by
  have h : G * (1 - A) = H := by rw [Matrix.mul_sub, Matrix.mul_one]; exact sub_eq_iff_eq_add.mpr hG
  calc
    G = (G * (1 - A)) * P.N := by rw [Matrix.mul_assoc, P.mul_inverse, Matrix.mul_one]
    _ = H * P.N := by rw [h]

theorem labor_existsUnique (H : Matrix m n ℝ) : ∃! G : Matrix m n ℝ, G = H + G * A :=
  ⟨P.labor H, P.labor_fixed H, fun _ h => P.labor_unique h⟩

/-- Equation (3.4): embodied requirements equal the labor of the gross plan. -/
theorem final_demand (H : Matrix m n ℝ) (y : n → ℝ) :
    P.labor H *ᵥ y = H *ᵥ (P.N *ᵥ y) := by rw [labor, mulVec_mulVec]

/-- Equation (3.5), including every occupation. -/
theorem unit_requirement (H : Matrix m n ℝ) (j : n) :
    (fun i => P.labor H i j) = (fun i => H i j) + P.labor H *ᵥ (fun k => A k j) := by
  funext i
  exact congrFun (congrFun (P.labor_fixed H) i) j

/-- Proposition 3.4: any supplied weights give the corresponding scalar account. -/
theorem scalar_fixed (H : Matrix m n ℝ) (ω : m → ℝ) :
    (P.labor H)ᵀ *ᵥ ω = Hᵀ *ᵥ ω + Aᵀ *ᵥ ((P.labor H)ᵀ *ᵥ ω) := by
  conv_lhs => rw [P.labor_fixed H]
  rw [transpose_add, add_mulVec, transpose_mul, mulVec_mulVec]

/-- Proposition 3.4 also asserts uniqueness of the supplied-weight scalar account. -/
theorem scalar_unique (H : Matrix m n ℝ) (ω : m → ℝ) {v : n → ℝ}
    (hv : v = Hᵀ *ᵥ ω + Aᵀ *ᵥ v) : v = (P.labor H)ᵀ *ᵥ ω := by
  have h : (1 - Aᵀ) *ᵥ v = Hᵀ *ᵥ ω := by
    rw [sub_mulVec, one_mulVec]
    exact sub_eq_iff_eq_add.mpr hv
  have hi : P.Nᵀ * (1 - Aᵀ) = 1 := by
    simpa only [transpose_mul, transpose_sub, transpose_one] using
      congrArg Matrix.transpose P.mul_inverse
  have hh := congrArg (fun w => P.Nᵀ *ᵥ w) h
  rw [mulVec_mulVec, hi, one_mulVec] at hh
  simpa only [labor, transpose_mul, mulVec_mulVec] using hh

theorem scalar_existsUnique (H : Matrix m n ℝ) (ω : m → ℝ) :
    ∃! v : n → ℝ, v = Hᵀ *ᵥ ω + Aᵀ *ᵥ v :=
  ⟨(P.labor H)ᵀ *ᵥ ω, P.scalar_fixed H ω, fun _ hv => P.scalar_unique H ω hv⟩

end Productive

/-- Inverse uniqueness makes the certificate's chosen inverse immaterial. -/
lemma inverse_unique {A N N' : Matrix n n ℝ}
    (hN : N * (1 - A) = 1) (hN' : (1 - A) * N' = 1) : N = N' := by
  calc
    N = N * ((1 - A) * N') := by rw [hN', Matrix.mul_one]
    _ = N' := by rw [← Matrix.mul_assoc, hN, Matrix.one_mul]

end Research

module

public import MarxLeanProof.Basic

@[expose] public section
set_option autoImplicit false

/-! # Sensitivity, project accounts, inventories, and boundary elimination
PDF Propositions 3.5, 5.1, 7.1, A.1 and C.8. -/
namespace Research
open Matrix
open scoped BigOperators Research
set_option linter.unusedSectionVars false
variable {n m o p : Type*} [Fintype n] [Fintype m] [Fintype o] [Fintype p]
  [DecidableEq n] [DecidableEq m] [DecidableEq o] [DecidableEq p]

/-- Exact finite-change identity (3.9), with no differentiability assumption. -/
theorem labor_difference {A A' : Matrix n n ℝ} (P : Productive A) (P' : Productive A')
    (H H' : Matrix m n ℝ) :
    P'.labor H' - P.labor H = (H' - H + P.labor H * (A' - A)) * P'.N := by
  have h : (P'.labor H' - P.labor H) * (1 - A') =
      H' - H + P.labor H * (A' - A) := by
    rw [Matrix.sub_mul, P'.labor_balance, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sub]
    have hg := P.labor_balance H
    rw [Matrix.mul_sub, Matrix.mul_one] at hg
    calc
      _ = H' - (P.labor H - P.labor H * A) +
          (P.labor H * A' - P.labor H * A) := by abel
      _ = _ := by rw [hg]
  calc
    _ = ((P'.labor H' - P.labor H) * (1 - A')) * P'.N := by
      rw [Matrix.mul_assoc, P'.mul_inverse, Matrix.mul_one]
    _ = _ := by rw [h]

/-- Entrywise monotonicity once both inverse certificates are supplied. -/
theorem labor_monotone {A A' : Matrix n n ℝ} (P : Productive A) (P' : Productive A')
    {H H' : Matrix m n ℝ} (hH : 0 ≤ H) (hA : A ≤ A') (hHH : H ≤ H') :
    P.labor H ≤ P'.labor H' := by
  apply sub_nonneg.mp
  rw [labor_difference P P']
  exact mm_nonneg (add_nonneg (sub_nonneg.mpr hHH)
    (mm_nonneg (P.labor_nonneg hH) (sub_nonneg.mpr hA))) P'.inverse_nonneg

/-- Solving the differentiated balance yields (3.8). The differentiability of a
particular parametrization is a separate hypothesis, not encoded by this identity. -/
theorem differential_balance {A : Matrix n n ℝ} (P : Productive A)
    (G dG dH : Matrix m n ℝ) (dA : Matrix n n ℝ)
    (h : dG * (1 - A) = dH + G * dA) :
    dG = (dH + G * dA) * P.N := by
  rw [← h, Matrix.mul_assoc, P.mul_inverse, Matrix.mul_one]

/-- Fresh project input reproduction, Proposition 5.1. -/
def projectLabor (G : Matrix m n ℝ) (a : n → ℝ) (h : m → ℝ) : m → ℝ := h + G *ᵥ a

theorem project_fresh {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (a : n → ℝ) (h : m → ℝ) :
    projectLabor (P.labor H) a h = h + H *ᵥ (P.N *ᵥ a) := by
  rw [projectLabor, P.final_demand]

/-- Nonnegative direct hours and inputs give nonnegative fresh project requirements. -/
theorem project_nonneg {G : Matrix m n ℝ} {a : n → ℝ} {h : m → ℝ}
    (hG : 0 ≤ G) (ha : 0 ≤ a) (hh : 0 ≤ h) : 0 ≤ projectLabor G a h :=
  add_nonneg hh (mv_nonneg hG ha)

/-- One-stage inventory reconciliation (7.4), including signed stock changes. -/
theorem inventory_reconciliation {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (J : Matrix n p ℝ) (F : Matrix m p ℝ)
    (s s' x y : n → ℝ) (z : p → ℝ)
    (balance : s' = s + (1 - A) *ᵥ x - y - J *ᵥ z) :
    H *ᵥ x + F *ᵥ z = P.labor H *ᵥ (y + J *ᵥ z + s' - s) + F *ᵥ z := by
  have h : y + J *ᵥ z + s' - s = (1 - A) *ᵥ x := by rw [balance]; abel
  rw [h, mulVec_mulVec, P.labor_balance]

/-- Constant-context telescoping in (7.5). -/
theorem inventory_telescope (G : Matrix m n ℝ) (s : ℕ → n → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, G *ᵥ (s (t + 1) - s t)) = G *ᵥ (s T - s 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, ← mulVec_add]
    congr 1
    abel

/-- Equation 7.5: actual chronological labor equals constant-context final
requirements, project requirements, and the signed terminal stock adjustment. -/
theorem inventory_horizon {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (J : ℕ → Matrix n p ℝ) (F : ℕ → Matrix m p ℝ)
    (s x y : ℕ → n → ℝ) (z : ℕ → p → ℝ) (T : ℕ)
    (balance : ∀ t, s (t + 1) = s t + (1 - A) *ᵥ x t - y t - J t *ᵥ z t) :
    (∑ t ∈ Finset.range T, (H *ᵥ x t + F t *ᵥ z t)) =
      (∑ t ∈ Finset.range T, (P.labor H *ᵥ y t + (F t + P.labor H * J t) *ᵥ z t)) +
        P.labor H *ᵥ (s T - s 0) := by
  calc
    _ = ∑ t ∈ Finset.range T,
        ((P.labor H *ᵥ y t + (F t + P.labor H * J t) *ᵥ z t) +
          P.labor H *ᵥ (s (t + 1) - s t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [inventory_reconciliation P H (J t) (F t) _ _ _ _ _ (balance t)]
      simp only [mulVec_add, mulVec_sub, add_mulVec, mulVec_mulVec]
      abel
    _ = _ := by rw [Finset.sum_add_distrib, inventory_telescope]

/-- Appendix A, block elimination from the two full labor equations. -/
theorem boundary_labor
    (ALL : Matrix n n ℝ) (ALO : Matrix n o ℝ) (AOL : Matrix o n ℝ)
    {AOO : Matrix o o ℝ} (PO : Productive AOO)
    (HL G_L : Matrix m n ℝ) (HO G_O : Matrix m o ℝ)
    (hL : G_L = HL + G_L * ALL + G_O * AOL)
    (hO : G_O = HO + G_L * ALO + G_O * AOO) :
    G_L = (HL + HO * PO.N * AOL) + G_L * (ALL + ALO * PO.N * AOL) := by
  have hG_O : G_O = (HO + G_L * ALO) * PO.N :=
    PO.labor_unique (by simpa [add_assoc] using hO)
  rw [hG_O] at hL
  simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc, add_left_comm, add_comm] using hL

/-- Exact retained labor formula (A.3). -/
theorem boundary_labor_solution
    (ALL : Matrix n n ℝ) (ALO : Matrix n o ℝ) (AOL : Matrix o n ℝ)
    {AOO : Matrix o o ℝ} (PO : Productive AOO)
    (PL : Productive (ALL + ALO * PO.N * AOL))
    (HL G_L : Matrix m n ℝ) (HO G_O : Matrix m o ℝ)
    (hL : G_L = HL + G_L * ALL + G_O * AOL)
    (hO : G_O = HO + G_L * ALO + G_O * AOO) :
    G_L = PL.labor (HL + HO * PO.N * AOL) :=
  PL.labor_unique (boundary_labor ALL ALO AOL PO HL G_L HO G_O hL hO)

/-- Audited C.8: eliminated reproduction inputs also contribute to effective
training labor. Deleting their rows alone does not preserve M. -/
theorem boundary_conversion (G_L : Matrix m n ℝ) (HO : Matrix m o ℝ)
    (ALO : Matrix n o ℝ) (NO : Matrix o o ℝ)
    (FL : Matrix n m ℝ) (FO : Matrix o m ℝ) (T : Matrix m m ℝ) :
    G_L * (FL + ALO * NO * FO) + (T + HO * NO * FO) =
      G_L * FL + ((HO + G_L * ALO) * NO) * FO + T := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- Appendix A.4: external final demand cannot be discarded. -/
theorem boundary_demand_labor (G_L : Matrix m n ℝ) (HO : Matrix m o ℝ)
    (ALO : Matrix n o ℝ) (NO : Matrix o o ℝ) (yL : n → ℝ) (yO : o → ℝ) :
    G_L *ᵥ yL + ((HO + G_L * ALO) * NO) *ᵥ yO =
      G_L *ᵥ (yL + ALO *ᵥ (NO *ᵥ yO)) + HO *ᵥ (NO *ᵥ yO) := by
  simp only [Matrix.add_mul, add_mulVec, mulVec_add, mulVec_mulVec, Matrix.mul_assoc]
  abel

end Research

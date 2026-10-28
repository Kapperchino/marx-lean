module
public import MarxLeanProof.Model
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! # v6.2 §§8–10: sparse analytical equations
These are reference requirements, not resource commitments or prices. `P` is
goods per occupation-hour; `J,F` are goods and additional hours per attempt.
-/
namespace Research.Simulator
open Matrix
open scoped BigOperators Research
variable {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m]

/-- Equation 8.3. A certificate is required; failure is never represented by zero. -/
def solve {K : Matrix n n ℝ} (C : Productive K) (b : n → ℝ) : n → ℝ := C.N *ᵥ b

theorem solve_fixed {K : Matrix n n ℝ} (C : Productive K) (b : n → ℝ) :
    solve C b = b + K *ᵥ solve C b := by
  simpa only [solve, add_comm] using C.reproduction b

theorem solve_unique {K : Matrix n n ℝ} (C : Productive K) {b q : n → ℝ}
    (h : q = b + K *ᵥ q) : q = solve C b :=
  C.reproduction_unique (h.trans (add_comm _ _))

theorem solve_nonneg {K : Matrix n n ℝ} (C : Productive K) {b : n → ℝ}
    (hb : 0 ≤ b) : 0 ≤ solve C b := mv_nonneg C.inverse_nonneg hb

/-- Equation 9.1 retains the lifetime convention for each target occupation. -/
noncomputable def perHourGoods (S E : Matrix n m ℝ) (lifetime : m → ℝ) : Matrix n m ℝ :=
  fun i j => S i j + E i j / lifetime j

noncomputable def perHourTraining (U : Matrix m m ℝ) (lifetime : m → ℝ) : Matrix m m ℝ :=
  fun i j => U i j / lifetime j

/-- The operator acts on goods then occupations, with exactly the PDF's transposes. -/
def coupledOperator (A : Matrix n n ℝ) (H : Matrix m n ℝ)
    (P : Matrix n m ℝ) (T : Matrix m m ℝ) : Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks Aᵀ Hᵀ Pᵀ Tᵀ

/-- Both updates read the old pair (Jacobi, not an in-place update). -/
def coupledStep (A : Matrix n n ℝ) (H : Matrix m n ℝ)
    (P : Matrix n m ℝ) (T : Matrix m m ℝ) (u : n → ℝ) (β : m → ℝ) :=
  (Aᵀ *ᵥ u + Hᵀ *ᵥ β, (1 : m → ℝ) + Pᵀ *ᵥ u + Tᵀ *ᵥ β)

theorem coupledStep_eq (A : Matrix n n ℝ) (H : Matrix m n ℝ)
    (P : Matrix n m ℝ) (T : Matrix m m ℝ) (u : n → ℝ) (β : m → ℝ) :
    Sum.elim (coupledStep A H P T u β).1 (coupledStep A H P T u β).2 =
      Sum.elim (0 : n → ℝ) (1 : m → ℝ) +
        coupledOperator A H P T *ᵥ Sum.elim u β := by
  ext i
  cases i <;> simp [coupledStep, coupledOperator, fromBlocks_mulVec, add_assoc]

/-- Eliminating goods gives exactly the existing occupational reproduction equation. -/
theorem coupled_reduction {A : Matrix n n ℝ} (C : Productive A)
    (H : Matrix m n ℝ) (P : Matrix n m ℝ) (T : Matrix m m ℝ)
    (u : n → ℝ) (β : m → ℝ) :
    (u = Aᵀ *ᵥ u + Hᵀ *ᵥ β ∧ β = 1 + Pᵀ *ᵥ u + Tᵀ *ᵥ β) ↔
      (u = (C.labor H)ᵀ *ᵥ β ∧ β = 1 + (C.labor H * P + T)ᵀ *ᵥ β) := by
  constructor
  · rintro ⟨hu, hb⟩
    have h := C.scalar_unique H β (hu.trans (add_comm _ _))
    refine ⟨h, ?_⟩
    simpa only [h, transpose_add, transpose_mul, add_mulVec, ← mulVec_mulVec,
      add_assoc] using hb
  · rintro ⟨rfl, hb⟩
    constructor
    · exact (C.scalar_fixed H β).trans (add_comm _ _)
    · simpa only [transpose_add, transpose_mul, add_mulVec, ← mulVec_mulVec,
        add_assoc] using hb

/-- Equation 9.5, conditional on the goods certificate, including the transpose. -/
theorem coupled_spectral_iff [Nonempty m] {A : Matrix n n ℝ} (C : Productive A)
    {H : Matrix m n ℝ} {P : Matrix n m ℝ} {T : Matrix m m ℝ}
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    SpectralProductive (coupledOperator A H P T) ↔
      SpectralProductive (C.labor H * P + T) := by
  rw [coupledOperator, ← fromBlocks_transpose, spectral_transpose]
  exact augmented_spectral_iff C hP hH hT

/-- The complete admissibility equivalence, including recovery of the goods
certificate from the coupled operator. The spectral forms follow from the
existing `spectral_iff_productive` for nonempty dimensions. -/
theorem coupled_productive_iff {A : Matrix n n ℝ} {H : Matrix m n ℝ}
    {P : Matrix n m ℝ} {T : Matrix m m ℝ}
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    Nonempty (Productive (coupledOperator A H P T)) ↔
      ∃ C : Productive A, Nonempty (Productive (C.labor H * P + T)) := by
  constructor
  · rintro ⟨Q⟩
    have full : Productive (fromBlocks A P H T) := by
      simpa only [coupledOperator, fromBlocks_transpose, transpose_transpose] using Q.transpose
    have swapped : Productive (fromBlocks T H P A) := by
      have he : (fromBlocks A P H T).submatrix (Equiv.sumComm m n) (Equiv.sumComm m n) =
          fromBlocks T H P A := by
        ext i j; cases i <;> cases j <;> rfl
      rw [← he]
      exact full.reindex (Equiv.sumComm m n)
    let C := swapped.external
    exact ⟨C, ⟨C.reproductionBlock full⟩⟩
  · rintro ⟨C, ⟨Q⟩⟩
    have full := C.augment hP hH hT Q
    exact ⟨by simpa only [coupledOperator, fromBlocks_transpose] using full.transpose⟩

theorem coupled_beta_ge_one {P : Matrix n m ℝ} {T : Matrix m m ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) {u : n → ℝ} {β : m → ℝ}
    (hu : 0 ≤ u) (hb : 0 ≤ β) (h : β = 1 + Pᵀ *ᵥ u + Tᵀ *ᵥ β) (i : m) :
    1 ≤ β i := by
  have hp := mv_nonneg (fun j k => hP k j) hu i
  have ht := mv_nonneg (fun j k => hT k j) hb i
  change 0 ≤ (Pᵀ *ᵥ u) i at hp
  change 0 ≤ (Tᵀ *ᵥ β) i at ht
  have he := congrFun h i
  change β i = 1 + (Pᵀ *ᵥ u) i + (Tᵀ *ᵥ β) i at he
  linarith

/-- Normalization divides both blocks by the same strictly positive reference. -/
theorem normalized_coupled {A : Matrix n n ℝ} {H : Matrix m n ℝ}
    {P : Matrix n m ℝ} {T : Matrix m m ℝ} {u : n → ℝ} {β : m → ℝ}
    (b : m) (hb : 0 < β b)
    (hu : u = Aᵀ *ᵥ u + Hᵀ *ᵥ β)
    (hβ : β = 1 + Pᵀ *ᵥ u + Tᵀ *ᵥ β) :
    let v := (β b)⁻¹ • u
    let α := (β b)⁻¹ • β
    α b = 1 ∧ v = Aᵀ *ᵥ v + Hᵀ *ᵥ α ∧
      α = (β b)⁻¹ • (1 : m → ℝ) + Pᵀ *ᵥ v + Tᵀ *ᵥ α := by
  dsimp only
  refine ⟨inv_mul_cancel₀ (ne_of_gt hb), ?_, ?_⟩
  · simpa only [smul_add, mulVec_smul] using congrArg ((β b)⁻¹ • ·) hu
  · simpa only [smul_add, mulVec_smul] using congrArg ((β b)⁻¹ • ·) hβ

/-- Equation 10.1. Failed and successful attempts have the same input account. -/
def researchValues (J : Matrix n r ℝ) (F : Matrix m r ℝ)
    (v : n → ℝ) (α : m → ℝ) : r → ℝ := Jᵀ *ᵥ v + Fᵀ *ᵥ α

def planValue (v : n → ℝ) (η : r → ℝ) (y : n → ℝ) (z : r → ℝ) : ℝ :=
  dotProduct v y + dotProduct η z

/-- Equations 10.2–10.4: the compact two-dot-product total equals raw hours
weighted once, when research inputs are freshly reproduced and excluded from y. -/
theorem planValue_eq_hours {A : Matrix n n ℝ} (C : Productive A)
    (H : Matrix m n ℝ) (J : Matrix n r ℝ) (F : Matrix m r ℝ)
    (α : m → ℝ) (y : n → ℝ) (z : r → ℝ) :
    planValue ((C.labor H)ᵀ *ᵥ α)
      (researchValues J F ((C.labor H)ᵀ *ᵥ α) α) y z =
      dotProduct α (H *ᵥ solve C (y + J *ᵥ z) + F *ᵥ z) := by
  unfold solve
  rw [← C.final_demand H (y + J *ᵥ z)]
  simp only [planValue, researchValues, dotProduct_add, add_dotProduct,
    dotProduct_mulVec, mulVec_transpose]
  ring

/-- Status tags preserve why a value is unavailable. None carries a fabricated value. -/
inductive Diagnostic (α : Type*) where
  | available (value : α)
  | missingData
  | inapplicable
  | inadmissible
  | unresolvedAccuracy
  deriving DecidableEq, Repr

/-- Equation 2.1: a labeled analytical comparator, not monetary profit. -/
noncomputable def surplusComparator (living requirement : ℝ) : ℝ := living - requirement

noncomputable def comparatorRate (living requirement : ℝ) : Option ℝ :=
  if 0 < requirement then some (surplusComparator living requirement / requirement) else none

/-- Context version tokens. Callers must advance the corresponding tokens when
inputs change; equality is required to reuse a cached value. -/
structure ContextVersion where
  techniques : ℕ
  units : ℕ
  classification : ℕ
  access : ℕ
  reproduction : ℕ
  occupations : ℕ
  referenceOccupation : ℕ
  researchCatalogue : ℕ
  capabilityGraph : ℕ
  numericalProfile : ℕ
  deriving DecidableEq, Repr

def cachedValue {α : Type*} (stored current : ContextVersion) (value : α) : Option α :=
  if stored = current then some value else none

theorem cachedValue_stale {α : Type*} {stored current : ContextVersion}
    (h : stored ≠ current) (value : α) : cachedValue stored current value = none := by
  simp [cachedValue, h]

end Research.Simulator

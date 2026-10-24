module
public import MarxLeanProof.Theorems
public import MarxLeanProof.Support
@[expose] public section
set_option autoImplicit false

/-! # Contexts, records, and the unified conditional specification
Boundary, installed equipment and recipe selection are supplied data. The algebra
does not infer feasibility, an adoption rule or the equal-residual assumption.
-/
namespace Research
open Matrix
open scoped BigOperators Research

/-- Definition 2.1. Metadata types are parameters so the accounting does not
impose an unmentioned equipment or route-selection model. -/
structure Context (boundary equipment selection producer capability : Type*) where
  upstreamBoundary : boundary
  stage : ℕ
  access : producer → Set capability
  installed : equipment
  selected : selection

variable {boundary equipment selection producer capability : Type*}

/-- Equation 5.2: a realized project grants its results to its implementer. -/
def grantResults [DecidableEq producer]
    (C : Context boundary equipment selection producer capability)
    (f : producer) (outcome : Set capability) :
    Context boundary equipment selection producer capability :=
  { C with access := Function.update C.access f (C.access f ∪ outcome) }

theorem grantResults_implementer [DecidableEq producer]
    (C : Context boundary equipment selection producer capability) (f : producer)
    (outcome : Set capability) : (grantResults C f outcome).access f = C.access f ∪ outcome := by
  simp [grantResults]

theorem grantResults_other [DecidableEq producer]
    (C : Context boundary equipment selection producer capability) (f g : producer)
    (outcome : Set capability) (h : g ≠ f) :
    (grantResults C f outcome).access g = C.access g := by
  simp [grantResults, h]

theorem grantResults_reusable [DecidableEq producer]
    (C : Context boundary equipment selection producer capability) (f g : producer)
    (outcome : Set capability) : C.access g ⊆ (grantResults C f outcome).access g := by
  by_cases h : g = f
  · subst g; rw [grantResults_implementer]; exact Set.subset_union_left
  · rw [grantResults_other C f g outcome h]

theorem grantResults_empty [DecidableEq producer]
    (C : Context boundary equipment selection producer capability) (f : producer) :
    grantResults C f ∅ = C := by simp [grantResults]

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- A whole attempt has physical inputs and direct hours even if its outcome is empty. -/
structure Project (n m producer capability : Type*) where
  implementer : producer
  prerequisites : Set capability
  inputs : n → ℝ
  directHours : m → ℝ
  inputs_nonneg : 0 ≤ inputs
  hours_nonneg : 0 ≤ directHours

def Project.Eligible (p : Project n m producer capability)
    (C : Context boundary equipment selection producer capability) : Prop :=
  p.prerequisites ⊆ C.access p.implementer

/-- The context stays attached to the occupational and Boolean accounts, 4.4.
The selected node type already represents the available catalogue. -/
structure ValuationRecord (context : Type*) (m capability : Type*) where
  contextData : context
  hours : m → ℝ
  supportingCapabilities : Set capability

def valuation {context : Type*} (C : context) {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (D : capability → n → Prop) (B : n → n → Prop) (j : n) :
    ValuationRecord context m capability :=
  ⟨C, fun r => P.labor H r j, fun k => Capability.closure D B k j⟩

/-- The numeric part of the unified specification (C.19) is uniquely determined
by the selected recipes, reproduction inputs and the explicit residual axiom. -/
theorem unified_unique {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (F : Matrix n m ℝ) (T : Matrix m m ℝ)
    (Q : Productive (P.labor H * F + T)ᵀ) (b : m) :
    ∃! result : Matrix m n ℝ × ((m → ℝ) × ℝ),
      result.1 = H + result.1 * A ∧
      EqualResidual (result.1 * F + T) b result.2.1 result.2.2 := by
  refine ⟨(P.labor H, Conversion.alpha Q b, Conversion.kappa Q b),
    ⟨P.labor_fixed H, Conversion.satisfies Q b⟩, ?_⟩
  rintro ⟨G, α, κ⟩ ⟨hG, hα⟩
  have hg := P.labor_unique hG
  dsimp only at hg hα ⊢
  subst G
  obtain ⟨ha, hk⟩ := Conversion.unique Q b hα
  exact Prod.ext rfl (Prod.ext ha hk)

end Research

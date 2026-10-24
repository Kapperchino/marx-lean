module
public import MarxLeanProof.Conversion
public import MarxLeanProof.Capabilities
public import MarxLeanProof.Accounting
@[expose] public section
set_option autoImplicit false
noncomputable section

/-! # Exact examples and counterexamples from the PDF
All arithmetic below is over the reals with exact rational constants, proved
by Lean's kernel-checked normalization. No floating-point or native-decide oracle.
-/
namespace Research.Examples
open Matrix
open scoped BigOperators Research

/- Section 8.1: steel, machine, widget. -/
def physicalA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 10, 1; 0, 0, 1/100; 0, 0, 0]
def physicalH : Matrix (Fin 1) (Fin 3) ℝ := !![2, 20, 1]
def physicalG : Matrix (Fin 1) (Fin 3) ℝ := !![2, 40, 17/5]

theorem physical_nilpotent : physicalA ^ 3 = 0 := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [physicalA, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ])
theorem physical_balance : physicalG = physicalH + physicalG * physicalA := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [physicalG, physicalH, physicalA, Matrix.mul_apply, Fin.sum_univ_succ])
theorem physical_inverse : (1 - physicalA) * (1 + physicalA + physicalA ^ 2) = 1 := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [physicalA, pow_succ, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ])

/- Section 8.2: fresh development, copies, and service. -/
def softwareA : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1/100, 10; 0, 0, 1/100000, 1/1000; 0, 0, 0, 0; 0, 0, 0, 0]
def softwareH : Matrix (Fin 1) (Fin 4) ℝ := !![1/50, 100, 11/1250, 1/5]
def softwareG : Matrix (Fin 1) (Fin 4) ℝ := !![1/50, 100, 1/100, 1/2]

theorem software_nilpotent : softwareA ^ 2 = 0 := by (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [softwareA, pow_two, Matrix.mul_apply, Fin.sum_univ_succ])
theorem software_balance : softwareG = softwareH + softwareG * softwareA := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [softwareG, softwareH, softwareA, Matrix.mul_apply, Fin.sum_univ_succ])
theorem release_development : (800 : ℝ) + 1000 * (1/50) + (9/5) * 100 = 1000 := by norm_num
theorem development_and_copies : (1000 : ℝ) + 1000 * (1/100) = 1010 := by norm_num

/- Sections 8.3–8.4: occupational distinctions and the material diamond. -/
def twoA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 0, 0]
def twoH : Matrix (Fin 2) (Fin 2) ℝ := !![3, 1; 0, 2]
def twoG : Matrix (Fin 2) (Fin 2) ℝ := !![3, 7; 0, 2]
theorem two_balance : twoG = twoH + twoG * twoA := by (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [twoA, twoH, twoG, Matrix.mul_apply, Fin.sum_univ_succ])
theorem supplied_weights : twoGᵀ *ᵥ ![1, 3] = ![3, 13] := by (ext i; fin_cases i <;> norm_num [twoG, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])

def diamondA : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 1, 0; 0, 0, 0, 1; 0, 0, 0, 1; 0, 0, 0, 0]
def diamondG : Matrix (Fin 1) (Fin 4) ℝ := !![1, 1, 1, 2]
theorem diamond_materials : diamondG = !![1, 0, 0, 0] + diamondG * diamondA := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [diamondG, diamondA, Matrix.mul_apply, Fin.sum_univ_succ])
def diamondB (i j : Fin 4) : Prop := (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 3)
instance : DecidableRel diamondB := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
theorem diamond_capability : Capability.iterate {0} diamondB 3 = {0, 1, 2, 3} := by decide

/- Section 8.5: shared missing prerequisites and a satisfied stopping point. -/
def researchEdge (j i : Fin 3) : Prop := i = 0 ∧ (j = 1 ∨ j = 2)
instance : DecidableRel researchEdge := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
theorem shared_prerequisite : Capability.iterate {1, 2} researchEdge 2 = {0, 1, 2} := by decide
theorem shared_hours : (4 : ℝ) + 6 + 8 = 18 ∧ (4 + 6) + (4 + 8) = 22 := by norm_num
def satisfiedEdge (j i : Fin 3) : Prop := i ≠ 0 ∧ researchEdge j i
instance : DecidableRel satisfiedEdge := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
theorem satisfied_stops : Capability.iterate {1, 2} satisfiedEdge 2 = {1, 2} := by decide
theorem satisfied_hours : (6 : ℝ) + 8 = 14 := by norm_num

/- C.6–C.7: the complete six-output conversion example. -/
def exampleA : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,0,0,0,0,0; 0,0,0,0,0,0; 0,0,0,2,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0]
def exampleH : Matrix (Fin 2) (Fin 6) ℝ := !![1,0,3,1,1/100,1/5; 0,1,0,2,1/500,1/10]
def exampleG : Matrix (Fin 2) (Fin 6) ℝ := !![1,0,3,7,1/100,1/5; 0,1,0,2,1/500,1/10]
def exampleS : Matrix (Fin 6) (Fin 2) ℝ := !![1/5,1/5; 0,0; 0,0; 0,0; 0,0; 0,0]
def exampleE : Matrix (Fin 6) (Fin 2) ℝ := !![0,2000; 400,3000; 0,0; 0,0; 0,0; 0,0]
def exampleU : Matrix (Fin 2) (Fin 2) ℝ := !![0,0; 600,2000]
def lifetimeInverse : Matrix (Fin 2) (Fin 2) ℝ := !![1/20000,0; 0,1/20000]
def exampleM : Matrix (Fin 2) (Fin 2) ℝ := !![1/5,3/10; 1/20,1/4]
def exampleW : Matrix (Fin 2) (Fin 2) ℝ := !![50/39,10/117; 20/39,160/117]
def exampleBeta : Fin 2 → ℝ := ![160/117, 220/117]
def exampleAlpha : Fin 2 → ℝ := ![1, 11/8]
def exampleValues : Fin 6 → ℝ := ![1,11/8,3,39/4,51/4000,27/80]

theorem example_nilpotent : exampleA ^ 2 = 0 := by (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleA, pow_two, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_goods_balance : exampleG = exampleH + exampleG * exampleA := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleG, exampleH, exampleA, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_provisioning : exampleG * exampleS = !![1/5,1/5; 0,0] := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleG, exampleS, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_training : (exampleG * exampleE + exampleU) * lifetimeInverse = !![0,1/10; 1/20,1/4] := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleG, exampleE, exampleU, lifetimeInverse, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_reproduction : reproductionMatrix exampleG exampleS exampleE exampleU lifetimeInverse = exampleM := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [reproductionMatrix, exampleG, exampleS, exampleE, exampleU, lifetimeInverse, exampleM, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_inverse_left : exampleW * (1 - exampleMᵀ) = 1 := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleW, exampleM, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_inverse_right : (1 - exampleMᵀ) * exampleW = 1 := by
  (ext i j; fin_cases i; all_goals fin_cases j; all_goals norm_num [exampleW, exampleM, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_succ])

def exampleProductive : Productive exampleMᵀ where
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [exampleM]
  N := exampleW
  inverse_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [exampleW]
  inverse_mul := example_inverse_left
  mul_inverse := example_inverse_right

theorem example_beta : Conversion.beta exampleProductive = exampleBeta := by
  (ext i; fin_cases i <;> norm_num [Conversion.beta, exampleProductive, exampleW, exampleBeta, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_alpha : Conversion.alpha exampleProductive 0 = exampleAlpha := by
  rw [Conversion.alpha, Conversion.kappa, example_beta]
  (ext i; fin_cases i <;> norm_num [exampleBeta, exampleAlpha, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_residual : exampleAlpha - exampleMᵀ *ᵥ exampleAlpha = (117/160 : ℝ) • (1 : Fin 2 → ℝ) := by
  (ext i; fin_cases i <;> norm_num [exampleAlpha, exampleM, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_burden : exampleMᵀ *ᵥ exampleAlpha = ![43/160,103/160] := by
  (ext i; fin_cases i <;> norm_num [exampleAlpha, exampleM, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_values : exampleGᵀ *ᵥ exampleAlpha = exampleValues := by
  (ext i; fin_cases i <;> norm_num [exampleG, exampleAlpha, exampleValues, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_ratio : exampleAlpha 1 / exampleAlpha 0 = 11/8 := by norm_num [exampleAlpha]
theorem example_project_hours : projectLabor exampleG ![5,2,0,0,0,0] ![10,20] = ![15,22] := by
  (ext i; fin_cases i <;> norm_num [projectLabor, exampleG, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem example_project_value : dotProduct exampleAlpha ![15,22] = 181/4 := by
  norm_num [exampleAlpha, dotProduct, Fin.sum_univ_succ]

/- Audited boundary and unit counterexamples. -/
def naiveM : Matrix (Fin 2) (Fin 2) ℝ := !![0,0; 3/100,1/10]
theorem naive_deletion_residual : ![1,(100/93 : ℝ)] - naiveMᵀ *ᵥ ![1,100/93] =
    (30/31 : ℝ) • (1 : Fin 2 → ℝ) := by (ext i; fin_cases i <;> norm_num [naiveM, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem naive_deletion_changes_ratio : (100/93 : ℝ) ≠ 11/8 := by norm_num

def hoursToDays : Matrix (Fin 2) (Fin 2) ℝ := !![1,0; 0,8]
def daysToHours : Matrix (Fin 2) (Fin 2) ℝ := !![1,0; 0,1/8]
theorem day_weights : hoursToDays *ᵥ exampleAlpha = ![1,11] := by
  (ext i; fin_cases i <;> norm_num [hoursToDays, exampleAlpha, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem day_residual : ![1,(11 : ℝ)] - (daysToHours * exampleM * hoursToDays)ᵀ *ᵥ ![1,11] =
    (117/160 : ℝ) • ![1,8] := by (ext i; fin_cases i <;> norm_num [daysToHours, exampleM, hoursToDays, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem day_values : (daysToHours * exampleG)ᵀ *ᵥ ![1,11] = exampleValues := by
  (ext i; fin_cases i <;> norm_num [daysToHours, exampleG, exampleValues, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem unequal_units_break_equal_numeric_residual :
    (117/160 : ℝ) • (![1,8] : Fin 2 → ℝ) ≠ (117/160 : ℝ) • (1 : Fin 2 → ℝ) := by
  intro h
  have := congrFun h 1
  norm_num at this

theorem alternative_residual : ![1,(38/17 : ℝ)] - exampleMᵀ *ᵥ ![1,38/17] =
    (117/170 : ℝ) • (![1,2] : Fin 2 → ℝ) := by (ext i; fin_cases i <;> norm_num [exampleM, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem alternative_residual_changes_ratio : (38/17 : ℝ) ≠ 11/8 := by norm_num

def provisioningOnly : Matrix (Fin 2) (Fin 2) ℝ := !![1/5,0; 0,2/5]
theorem provisioning_alone_changes_weights :
    ![1,(4/3 : ℝ)] - provisioningOnlyᵀ *ᵥ ![1,4/3] = (4/5 : ℝ) • (1 : Fin 2 → ℝ) := by
  (ext i; fin_cases i <;> norm_num [provisioningOnly, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
theorem same_hours_unequal_weights : (1 : ℝ) ≠ 4/3 := by norm_num

/- The core model's cautions are exact counterexamples, not extra axioms. -/
theorem zero_labor_does_not_imply_productivity : (0 : ℝ) = 0 + 0 * 2 ∧ ¬ ∃ x : ℝ, 0 ≤ x ∧ x = 2*x + 1 := by
  constructor
  · norm_num
  · rintro ⟨x,hx,he⟩; linarith
theorem inventory_double_count : (1 : ℝ) + 2 = 3 ∧ 1 + (2 + 1) = 4 ∧ (3 : ℝ) ≠ 4 := by norm_num
theorem changing_context_stocks_do_not_telescope :
    (1 : ℝ) * (1 - 0) + 2 * (0 - 1) ≠ 2 * (0 - 0) := by norm_num
theorem normalized_weights_need_not_increase :
    ![1,(1/2 : ℝ)] - (!![1/2,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ![1,1/2] =
      (1/2 : ℝ) • (1 : Fin 2 → ℝ) ∧ (1/2 : ℝ) < 1 := by
  constructor
  · (ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ])
  · norm_num

end Research.Examples

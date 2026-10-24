module
public import MarxLeanProof.Accounting
public import MarxLeanProof.Conversion
@[expose] public section
set_option autoImplicit false

/-! # Differentiable changes in a fixed regime (3.5 and C.7)
All derivative statements quantify over genuinely differentiable real curves.
The curves must keep the same coordinates and satisfy the indicated balances.
-/
namespace Research
open Matrix Filter
open scoped BigOperators Research Topology
set_option linter.unusedSectionVars false
variable {n m o : Type*} [Fintype n] [Fintype m] [Fintype o]
  [DecidableEq n] [DecidableEq m] [DecidableEq o]

def MatrixDeriv (A : ℝ → Matrix m n ℝ) (dA : Matrix m n ℝ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => A s i j) (dA i j) t

def VectorDeriv (a : ℝ → m → ℝ) (da : m → ℝ) (t : ℝ) : Prop :=
  ∀ i, HasDerivAt (fun s => a s i) (da i) t

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- Inversion is differentiable at a productive point. Only derivatives of the
coefficient curve are assumed; the derivative of its inverse is constructed. -/
theorem MatrixDeriv.leontiefInverse {A : ℝ → Matrix n n ℝ} {dA : Matrix n n ℝ} {t : ℝ}
    (hA : MatrixDeriv A dA t) (P : Productive (A t)) :
    MatrixDeriv (fun s => (1 - A s)⁻¹) (P.N * dA * P.N) t := by
  let u : (Matrix n n ℝ)ˣ :=
    { val := 1 - A t
      inv := P.N
      val_inv := P.mul_inverse
      inv_val := P.inverse_mul }
  have ha : HasDerivAt A dA t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hA i))
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt t (ha.const_sub 1)
  have hu : (↑u⁻¹ : Matrix n n ℝ) = P.N := rfl
  have hi' : HasDerivAt (fun s => (1 - A s)⁻¹) (P.N * dA * P.N) t := by
    simpa! only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse,
      _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hu,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg] using hi
  intro i j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hi' i) j

lemma MatrixDeriv.mul {A : ℝ → Matrix m n ℝ} {B : ℝ → Matrix n o ℝ}
    {dA : Matrix m n ℝ} {dB : Matrix n o ℝ} {t : ℝ}
    (ha : MatrixDeriv A dA t) (hb : MatrixDeriv B dB t) :
    MatrixDeriv (fun s => A s * B s) (dA * B t + A t * dB) t := by
  intro i j
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (ha i k).mul (hb k j))
  simpa! only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using hh

lemma MatrixDeriv.mulVec {A : ℝ → Matrix m n ℝ} {b : ℝ → n → ℝ}
    {dA : Matrix m n ℝ} {db : n → ℝ} {t : ℝ}
    (ha : MatrixDeriv A dA t) (hb : VectorDeriv b db t) :
    VectorDeriv (fun s => A s *ᵥ b s) (dA *ᵥ b t + A t *ᵥ db) t := by
  intro i
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (ha i k).mul (hb k))
  simpa! only [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using hh

/-- Equation 3.8 with existence of the derivative, directly from A and H. -/
theorem labor_hasDerivAt {A : ℝ → Matrix n n ℝ} {H : ℝ → Matrix m n ℝ}
    {dA : Matrix n n ℝ} {dH : Matrix m n ℝ} {t : ℝ} (P : Productive (A t))
    (hA : MatrixDeriv A dA t) (hH : MatrixDeriv H dH t) :
    MatrixDeriv (fun s => H s * (1 - A s)⁻¹) ((dH + P.labor (H t) * dA) * P.N) t := by
  have hd := hH.mul (hA.leontiefInverse P)
  simpa only [← P.inverse_eq, Productive.labor, Matrix.add_mul, Matrix.mul_assoc] using hd

/-- The actual derivative formula dG=(dH+GdA)N, equation 3.8. -/
theorem labor_derivative {A : ℝ → Matrix n n ℝ} {H G : ℝ → Matrix m n ℝ}
    {dA : Matrix n n ℝ} {dH dG : Matrix m n ℝ} {t : ℝ} (P : Productive (A t))
    (hA : MatrixDeriv A dA t) (hH : MatrixDeriv H dH t) (hG : MatrixDeriv G dG t)
    (balance : ∀ s, G s = H s + G s * A s) : dG = (dH + G t * dA) * P.N := by
  have he : dG = dH + (dG * A t + G t * dA) := by
    ext i j
    have hd := (hH i j).fun_add (hG.mul hA i j)
    have hf : (fun s => H s i j + (G s * A s) i j) = (fun s => G s i j) := by
      funext s; exact (congrFun (congrFun (balance s) i) j).symm
    rw [hf] at hd
    exact (hG i j).unique hd
  apply differential_balance P (G t) dG dH dA
  rw [Matrix.mul_sub, Matrix.mul_one]
  exact sub_eq_iff_eq_add.mpr (he.trans (by abel))

/-- The coefficient formula following 3.8: the (i,k) direction contributes
G[r,i] N[k,j] to the (r,j) occupational requirement. -/
theorem coefficient_sensitivity (G : Matrix m n ℝ) (N : Matrix n n ℝ) (r : m) (i k j : n) :
    (G * Matrix.single i k (1 : ℝ) * N) r j = G r i * N k j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    rw [Matrix.mul_single_apply_of_ne (1 : ℝ) i k r l hl G, zero_mul]
  · simp

/-- The partial derivative in 3.8, with the perturbed coefficient and evaluation
point specified explicitly. The algebraic extension is defined near any productive A. -/
theorem coefficient_hasDerivAt {A : Matrix n n ℝ} (P : Productive A)
    (H : Matrix m n ℝ) (r : m) (i k j : n) :
    HasDerivAt (fun s : ℝ => (H * (1 - (A + s • Matrix.single i k (1 : ℝ)))⁻¹) r j)
      (P.labor H r i * P.N k j) 0 := by
  have hA : MatrixDeriv (fun s : ℝ => A + s • Matrix.single i k (1 : ℝ))
      (Matrix.single i k (1 : ℝ)) 0 := by
    intro a b
    simpa! only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.single i k (1 : ℝ) a b)).const_add (A a b)
  have hH : MatrixDeriv (fun _ : ℝ => H) 0 0 := fun a b => hasDerivAt_const 0 (H a b)
  have P0 : Productive (A + (0 : ℝ) • Matrix.single i k (1 : ℝ)) := by simpa using P
  have hd := labor_hasDerivAt P0 hA hH r j
  have hn : P0.N = P.N := inverse_unique P0.inverse_mul (by simpa using P.mul_inverse)
  simpa only [zero_add, Productive.labor, hn, coefficient_sensitivity] using hd

/-- C.11's product rule for M=GF+T. -/
theorem reproduction_derivative {G : ℝ → Matrix m n ℝ} {F : ℝ → Matrix n m ℝ}
    {T : ℝ → Matrix m m ℝ} {dG : Matrix m n ℝ} {dF : Matrix n m ℝ}
    {dT : Matrix m m ℝ} {t : ℝ}
    (hG : MatrixDeriv G dG t) (hF : MatrixDeriv F dF t) (hT : MatrixDeriv T dT t) :
    MatrixDeriv (fun s => G s * F s + T s) (dG * F t + G t * dF + dT) t :=
  fun i j => (hG.mul hF i j).add (hT i j)

/-- C.11: differentiate the unnormalized conversion solve. -/
theorem beta_derivative {M : ℝ → Matrix m m ℝ} {β : ℝ → m → ℝ}
    {dM : Matrix m m ℝ} {dβ : m → ℝ} {t : ℝ} (Q : Productive (M t)ᵀ)
    (hM : MatrixDeriv M dM t) (hβ : VectorDeriv β dβ t)
    (balance : ∀ s, β s - (M s)ᵀ *ᵥ β s = (1 : m → ℝ)) :
    dβ = Q.N *ᵥ (dMᵀ *ᵥ β t) := by
  have hMt : MatrixDeriv (fun s => (M s)ᵀ) dMᵀ t := fun i j => hM j i
  have he : dβ - (dMᵀ *ᵥ β t + (M t)ᵀ *ᵥ dβ) = 0 := by
    funext i
    have hd := (hβ i).fun_sub (hMt.mulVec hβ i)
    have hf : (fun s => β s i - ((M s)ᵀ *ᵥ β s) i) = (fun _ => (1 : ℝ)) := by
      funext s; exact congrFun (balance s) i
    rw [hf] at hd
    exact hd.unique (hasDerivAt_const t 1)
  have he' : (1 - (M t)ᵀ) *ᵥ dβ = dMᵀ *ᵥ β t := by
    rw [sub_mulVec, one_mulVec]
    apply sub_eq_iff_eq_add.mpr
    have hh := sub_eq_zero.mp he
    exact hh
  rw [← he', mulVec_mulVec, Q.inverse_mul, one_mulVec]

/-- C.11 with existence of the beta derivative, requiring only derivatives of M. -/
theorem beta_hasDerivAt {M : ℝ → Matrix m m ℝ} {dM : Matrix m m ℝ} {t : ℝ}
    (Q : Productive (M t)ᵀ) (hM : MatrixDeriv M dM t) :
    VectorDeriv (fun s => (1 - (M s)ᵀ)⁻¹ *ᵥ (1 : m → ℝ))
      (Q.N *ᵥ (dMᵀ *ᵥ Conversion.beta Q)) t := by
  have hMt : MatrixDeriv (fun s => (M s)ᵀ) dMᵀ t := fun i j => hM j i
  have h1 : VectorDeriv (fun _ : ℝ => (1 : m → ℝ)) 0 t :=
    fun _ => hasDerivAt_const t 1
  have hd := (hMt.leontiefInverse Q).mulVec h1
  simpa only [mulVec_zero, add_zero, mulVec_mulVec, Matrix.mul_assoc, Conversion.beta] using hd

/-- C.11: derivative of reference-normalized weights. -/
theorem normalized_derivative {β : ℝ → m → ℝ} {dβ : m → ℝ} {t : ℝ}
    (hβ : VectorDeriv β dβ t) (b : m) (hb : β t b ≠ 0) :
    VectorDeriv (fun s i => β s i / β s b)
      (fun i => (dβ i - (β t i / β t b) * dβ b) / β t b) t := by
  intro i
  convert (hβ i).div (hβ b) hb using 1
  field_simp

/-- C.11: scalar values respond to both hours and weights. -/
theorem values_derivative {G : ℝ → Matrix m n ℝ} {α : ℝ → m → ℝ}
    {dG : Matrix m n ℝ} {dα : m → ℝ} {t : ℝ}
    (hG : MatrixDeriv G dG t) (hα : VectorDeriv α dα t) :
    VectorDeriv (fun s => (G s)ᵀ *ᵥ α s) (dGᵀ *ᵥ α t + (G t)ᵀ *ᵥ dα) t := by
  exact MatrixDeriv.mulVec (fun i j => hG j i) hα

/-- Corollary 6.2: the idealized copying limit is a continuity theorem. -/
theorem copying_limit {ι : Type*} {l : Filter ι} (G : Matrix m n ℝ)
    {a : ι → n → ℝ} {h : ι → m → ℝ} (ha : Tendsto a l (𝓝 0)) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun t => h t + G *ᵥ a t) l (𝓝 0) := by
  have hc : Continuous (fun x : n → ℝ => G *ᵥ x) := continuous_const.matrix_mulVec continuous_id
  simpa using hh.add (hc.continuousAt.tendsto.comp ha)

/-- C.12: forward error is bounded by the nonnegative inverse times the absolute residual. -/
theorem residual_error_bound {M : Matrix m m ℝ} (Q : Productive Mᵀ) (approx : m → ℝ) (i : m) :
    |(Conversion.beta Q - approx) i| ≤
      (Q.N *ᵥ (fun j => |(1 - (1 - Mᵀ) *ᵥ approx) j|)) i := by
  rw [residual_error Q approx]
  simp only [Matrix.mulVec, dotProduct]
  calc
    _ ≤ ∑ j, |Q.N i j * (1 - (1 - Mᵀ) *ᵥ approx) j| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (Q.inverse_nonneg i _)]

end Research

module
public import MarxLeanProof.Productivity
@[expose] public section
set_option autoImplicit false

/-! # The spectral-radius criterion (Theorem 3.1(i))
The spectral radius is taken over the complexification of the real matrix,
so non-real eigenvalues are included. Gelfand's formula supplies convergence;
no diagonalizability assumption is made.
-/
namespace Research
open Matrix Filter
open scoped BigOperators Research Topology Matrix.Norms.Operator ENNReal
set_option linter.unusedSectionVars false

/-- A general complex Banach-algebra version of the Neumann convergence criterion. -/
theorem summable_powers_of_radius_lt {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    [CompleteSpace R] (a : R) (h : spectralRadius ℂ a < 1) : Summable (fun k : ℕ => a ^ k) := by
  have hfin : spectralRadius ℂ a ≠ ⊤ := ne_of_lt (h.trans (by simp))
  have hradius : (spectralRadius ℂ a).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfin ENNReal.one_ne_top).mpr h
  obtain ⟨r, hr, hr1⟩ := exists_between hradius
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg.trans hr.le
  have ht := (ENNReal.continuousAt_toReal hfin).tendsto.comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
  have ht' : Tendsto (fun k : ℕ => ‖a ^ k‖ ^ (1 / (k : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a).toReal) := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using ht
  apply (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [ht'.eventually (gt_mem_nhds hr), eventually_gt_atTop 0] with k hk hk0
  have hb := (Real.rpow_inv_le_iff_of_pos (norm_nonneg (a ^ k)) hr0
    (Nat.cast_pos.mpr hk0 : (0 : ℝ) < k)).mp (by simpa only [one_div] using hk.le)
  simpa only [Real.rpow_natCast] using hb

/-- Convergence implies that the spectral radius is strictly below one. -/
theorem radius_lt_of_summable_powers {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    [CompleteSpace R] [NormOneClass R] (a : R)
    (hs : Summable (fun k : ℕ => a ^ k)) : spectralRadius ℂ a < 1 := by
  have hn : Tendsto (fun k : ℕ => ‖a ^ k‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hs.tendsto_atTop_zero.norm
  have he : ∀ᶠ k : ℕ in atTop, ‖a ^ k‖ < 1 := by
    simpa only [norm_zero] using hn.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨k, hk, hk0⟩ := (he.and (eventually_gt_atTop 0)).exists
  have hp : spectralRadius ℂ a ^ k < 1 :=
    (spectrum.spectralRadius_pow_le a k (Nat.ne_of_gt hk0)).trans_lt
      ((spectralRadius_le_nnnorm (𝕜 := ℂ) (a ^ k)).trans_lt (by exact_mod_cast hk))
  by_contra hnot
  have hge : 1 ≤ spectralRadius ℂ a := le_of_not_gt hnot
  have hpow : (1 : ℝ≥0∞) ≤ spectralRadius ℂ a ^ k := one_le_pow₀ hge
  exact (not_lt_of_ge hpow) hp

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal

lemma complexify_pow (A : Matrix n n ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k :=
  Matrix.map_pow A Complex.ofRealHom k

/-- The paper's spectral admissibility test, using all complex eigenvalues. -/
def SpectralProductive (A : Matrix n n ℝ) : Prop := spectralRadius ℂ (complexify A) < 1

lemma summable_complexify (A : Matrix n n ℝ) :
    Summable (fun k : ℕ => complexify A ^ k) ↔ Summable (fun k : ℕ => A ^ k) := by
  simp only [← complexify_pow]
  change Summable (fun k : ℕ => fun i j => ((A ^ k) i j : ℂ)) ↔
    Summable (fun k : ℕ => (A ^ k : n → n → ℝ))
  constructor
  · intro hs
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    exact Complex.summable_ofReal.mp (Pi.summable.mp (Pi.summable.mp hs i) j)
  · intro hs
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    exact Complex.summable_ofReal.mpr (Pi.summable.mp (Pi.summable.mp hs i) j)

/-- Theorem 3.1(i) ↔ (ii). -/
theorem spectral_iff_summable (A : Matrix n n ℝ) :
    SpectralProductive A ↔ Summable (fun k : ℕ => A ^ k) := by
  constructor
  · intro h
    exact (summable_complexify A).mp (summable_powers_of_radius_lt _ h)
  · intro hs
    exact radius_lt_of_summable_powers _ ((summable_complexify A).mpr hs)

/-- Theorem 3.1(i) ↔ (iii), linking all certificate-based results to ρ(A)<1. -/
theorem spectral_iff_productive {A : Matrix n n ℝ} (hA : 0 ≤ A) :
    SpectralProductive A ↔ Nonempty (Productive A) :=
  (spectral_iff_summable A).trans (productive_iff_summable hA).symm

/-- Construct the certified inverse directly from the paper's spectral hypothesis. -/
noncomputable def productiveOfSpectral {A : Matrix n n ℝ} (hA : 0 ≤ A)
    (hρ : SpectralProductive A) : Productive A :=
  productiveOfSummable hA ((spectral_iff_summable A).mp hρ)

/-- The spectral condition is invariant under transposition. -/
theorem spectral_transpose (A : Matrix n n ℝ) : SpectralProductive Aᵀ ↔ SpectralProductive A := by
  have hc : complexify Aᵀ = (complexify A)ᵀ := rfl
  unfold SpectralProductive
  rw [hc]
  unfold spectralRadius
  simp only [quasispectrum_eq_spectrum_union_zero, Matrix.spectrum_transpose]

/-- Similarity preserves the entire spectral radius, not just productivity. -/
theorem spectralRadius_change_units (A S T : Matrix n n ℝ)
    (hST : S * T = 1) (hTS : T * S = 1) :
    spectralRadius ℂ (complexify (T * A * S)) = spectralRadius ℂ (complexify A) := by
  have hm (X Y : Matrix n n ℝ) : complexify (X * Y) = complexify X * complexify Y :=
    Matrix.map_mul (f := Complex.ofRealHom)
  have h1 : complexify (1 : Matrix n n ℝ) = 1 :=
    Matrix.map_one Complex.ofReal (by simp) (by simp)
  let u : (Matrix n n ℂ)ˣ :=
    { val := complexify S
      inv := complexify T
      val_inv := by rw [← hm, hST, h1]
      inv_val := by rw [← hm, hTS, h1] }
  have hs : spectrum ℂ (complexify (T * A * S)) = spectrum ℂ (complexify A) := by
    rw [hm, hm]
    exact spectrum.units_conjugate' (R := ℂ) (a := complexify A) (u := u)
  simp only [spectralRadius_eq_of_unital, hs]

end Research

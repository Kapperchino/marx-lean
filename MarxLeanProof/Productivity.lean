module
public import MarxLeanProof.Basic
@[expose] public section
set_option autoImplicit false

/-! # Productive reproduction, Neumann series, and positive certificates
Theorem 3.1(ii)–(v) and the productivity part of Proposition 3.5.
-/
namespace Research
open Matrix Filter
open scoped BigOperators Research Topology
set_option linter.unusedSectionVars false
variable {n m : Type*} [Fintype n] [DecidableEq n]

lemma pow_nonneg {A : Matrix n n ℝ} (hA : 0 ≤ A) (k : ℕ) : 0 ≤ A ^ k := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih => rw [pow_succ]; exact mm_nonneg ih hA

/-- A convergent nonnegative Neumann series constructs a productive inverse. -/
noncomputable def productiveOfSummable {A : Matrix n n ℝ} (hA : 0 ≤ A)
    (hs : Summable (fun k : ℕ => A ^ k)) : Productive A where
  nonneg := hA
  N := ∑' k : ℕ, A ^ k
  inverse_nonneg := by
    intro i j
    have hij := Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum i) j
    exact hij.tsum_eq ▸ tsum_nonneg (fun k => pow_nonneg hA k i j)
  inverse_mul := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have h : (∑' k : ℕ, A ^ k) * A = ∑' k : ℕ, A ^ (k + 1) := by
      rw [← hs.tsum_mul_right]
      simp only [pow_succ]
    rw [h]
    have he := hs.tsum_eq_zero_add
    rw [pow_zero] at he
    exact sub_eq_iff_eq_add.mpr he
  mul_inverse := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    have h : A * (∑' k : ℕ, A ^ k) = ∑' k : ℕ, A ^ (k + 1) := by
      rw [← hs.tsum_mul_left]
      simp only [pow_succ']
    rw [h]
    have he := hs.tsum_eq_zero_add
    rw [pow_zero] at he
    exact sub_eq_iff_eq_add.mpr he

namespace Productive
variable {A : Matrix n n ℝ} (P : Productive A)
include P

/-- The finite remainder identity behind the series and the truncation bound. -/
theorem neumann_remainder (k : ℕ) :
    P.N = (∑ i ∈ Finset.range k, A ^ i) + A ^ k * P.N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ, Matrix.mul_assoc]
    conv_lhs => rw [ih]
    have hn : P.N = 1 + A * P.N := P.N_eq
    calc
      _ = (∑ i ∈ Finset.range k, A ^ i) + A ^ k * (1 + A * P.N) := by rw [← hn]
      _ = _ := by rw [Matrix.mul_add, Matrix.mul_one]; abel

/-- No convergence assumption is hidden in the inverse criterion. -/
theorem summable_powers : Summable (fun k : ℕ => A ^ k) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply summable_of_sum_range_le (c := P.N i j) (fun k => pow_nonneg P.nonneg k i j)
  intro k
  have h := congrFun (congrFun (P.neumann_remainder k) i) j
  have hn := mm_nonneg (pow_nonneg P.nonneg k) P.inverse_nonneg i j
  change 0 ≤ (A ^ k * P.N) i j at hn
  simp only [Matrix.add_apply, Matrix.sum_apply] at h
  linarith

/-- Equation (3.1). -/
theorem neumann_series : P.N = ∑' k : ℕ, A ^ k :=
  inverse_unique P.inverse_mul (productiveOfSummable P.nonneg P.summable_powers).mul_inverse

/-- Every partial labor account underestimates the complete account. -/
theorem labor_partial_le [Fintype m] [DecidableEq m]
    {H : Matrix m n ℝ} (hH : 0 ≤ H) (k : ℕ) :
    H * (∑ i ∈ Finset.range k, A ^ i) ≤ P.labor H := by
  have hN : (∑ i ∈ Finset.range k, A ^ i) ≤ P.N := by
    rw [P.neumann_remainder k]
    exact le_add_of_nonneg_right (mm_nonneg (pow_nonneg P.nonneg k) P.inverse_nonneg)
  exact mm_mono hH P.inverse_nonneg le_rfl hN

/-- Equation (3.3), including the infinite layer decomposition. -/
theorem labor_series [Fintype m] [DecidableEq m] (H : Matrix m n ℝ) :
    P.labor H = ∑' k : ℕ, H * A ^ k := by
  have hs := P.summable_powers.hasSum.map (Matrix.addMonoidHomMulLeft H)
    (continuous_const.matrix_mul continuous_id)
  change HasSum (fun k : ℕ => H * A ^ k) (H * ∑' k : ℕ, A ^ k) at hs
  rw [← P.neumann_series] at hs
  exact hs.tsum_eq.symm

end Productive

/-- A strictly positive contraction vector yields a summable Neumann series. -/
theorem summable_of_contraction {A : Matrix n n ℝ} (hA : 0 ≤ A)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hAw : A *ᵥ w ≤ c • w) : Summable (fun k : ℕ => A ^ k) := by
  have hpow : ∀ k : ℕ, A ^ k *ᵥ w ≤ c ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec]
      calc
        A *ᵥ (A ^ k *ᵥ w) ≤ A *ᵥ (c ^ k • w) := mv_mono hA ih
        _ = c ^ k • (A *ᵥ w) := mulVec_smul _ _ _
        _ ≤ c ^ k • (c • w) := by
          intro i
          exact mul_le_mul_of_nonneg_left (hAw i) (_root_.pow_nonneg hc k)
        _ = c ^ (k + 1) • w := by rw [smul_smul, pow_succ]
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply Summable.of_nonneg_of_le (fun k => pow_nonneg hA k i j)
    (f := fun k => (w i / w j) * c ^ k)
  · intro k
    have hterm : (A ^ k) i j * w j ≤ (A ^ k *ᵥ w) i := by
      exact Finset.single_le_sum (fun l _ => mul_nonneg (pow_nonneg hA k i l) (hw l).le)
        (Finset.mem_univ j)
    have hbound := hterm.trans (hpow k i)
    have ht := (le_div_iff₀ (hw j)).mpr hbound
    convert ht using 1; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · exact (summable_geometric_of_lt_one hc hc1).mul_left _

/-- The positive-vector criterion constructs the nonnegative inverse. -/
noncomputable def productiveOfWitness {A : Matrix n n ℝ} (hA : 0 ≤ A)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) (hAw : ∀ i, (A *ᵥ w) i < w i) : Productive A := by
  classical
  apply Classical.choice
  by_cases hn : Nonempty n
  · let := hn
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => (A *ᵥ w) i / w i)
      Finset.univ_nonempty
    let c := (A *ᵥ w) i / w i
    have hc : 0 ≤ c := div_nonneg (mv_nonneg hA (fun j => (hw j).le) i) (hw i).le
    have hc1 : c < 1 := (div_lt_one (hw i)).mpr (hAw i)
    refine ⟨productiveOfSummable hA (summable_of_contraction hA hw hc hc1 ?_)⟩
    intro j
    exact (div_le_iff₀ (hw j)).mp (hi j (Finset.mem_univ j))
  · have : IsEmpty n := not_nonempty_iff.mp hn
    exact ⟨{ nonneg := hA
             N := 1
             inverse_nonneg := by intro i; exact isEmptyElim i
             inverse_mul := Subsingleton.elim _ _
             mul_inverse := Subsingleton.elim _ _ }⟩

/-- Theorem 3.1(iii) ↔ (iv). -/
theorem productive_iff_witness {A : Matrix n n ℝ} (hA : 0 ≤ A) :
    Nonempty (Productive A) ↔ ∃ w : n → ℝ, (∀ i, 0 < w i) ∧ ∀ i, (A *ᵥ w) i < w i :=
  ⟨fun ⟨P⟩ => P.positive_witness, fun ⟨w, hw, hAw⟩ => ⟨productiveOfWitness hA w hw hAw⟩⟩

/-- Theorem 3.1(ii) ↔ (iii). -/
theorem productive_iff_summable {A : Matrix n n ℝ} (hA : 0 ≤ A) :
    Nonempty (Productive A) ↔ Summable (fun k : ℕ => A ^ k) :=
  ⟨fun ⟨P⟩ => P.summable_powers, fun hs => ⟨productiveOfSummable hA hs⟩⟩

/-- Smaller nonnegative ordinary requirements remain productive, Proposition 3.5. -/
noncomputable def productiveOfLe {A A' : Matrix n n ℝ} (P : Productive A)
    (hA' : 0 ≤ A') (h : A' ≤ A) : Productive A' := by
  apply Classical.choice
  obtain ⟨w, hw, hAw⟩ := P.positive_witness
  refine ⟨productiveOfWitness hA' w hw ?_⟩
  intro i
  apply lt_of_le_of_lt _ (hAw i)
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hw j).le

/-- Transposition preserves the productive-inverse criterion. -/
def Productive.transpose {A : Matrix n n ℝ} (P : Productive A) : Productive Aᵀ where
  nonneg := fun i j => P.nonneg j i
  N := P.Nᵀ
  inverse_nonneg := fun i j => P.inverse_nonneg j i
  inverse_mul := by simpa only [transpose_mul, transpose_sub, transpose_one] using congrArg Matrix.transpose P.mul_inverse
  mul_inverse := by simpa only [transpose_mul, transpose_sub, transpose_one] using congrArg Matrix.transpose P.inverse_mul

/-- Theorem 3.1(v), with every nonnegative demand quantified explicitly. -/
theorem productive_iff_reproduction {A : Matrix n n ℝ} (hA : 0 ≤ A) :
    Nonempty (Productive A) ↔
      ∀ y : n → ℝ, 0 ≤ y → ∃! x : n → ℝ, 0 ≤ x ∧ x = A *ᵥ x + y := by
  constructor
  · rintro ⟨P⟩ y hy
    exact P.reproduction_existsUnique hy
  · intro h
    obtain ⟨x, ⟨hx, he⟩, _⟩ := h 1 (by intro i; exact zero_le_one)
    have hn := mv_nonneg hA hx
    apply (productive_iff_witness hA).mpr
    refine ⟨x, ?_, ?_⟩
    · intro i
      have hi := congrFun he i
      have hni := hn i
      change x i = (A *ᵥ x) i + 1 at hi
      change 0 ≤ (A *ᵥ x) i at hni
      linarith
    · intro i
      have hi := congrFun he i
      change x i = (A *ᵥ x) i + 1 at hi
      linarith

/-- Relabeling finite coordinates preserves productivity. -/
noncomputable def Productive.reindex {o : Type*} [Fintype o] [DecidableEq o]
    {A : Matrix n n ℝ} (P : Productive A) (e : o ≃ n) : Productive (A.submatrix e e) := by
  apply Classical.choice
  obtain ⟨w, hw, hAw⟩ := P.positive_witness
  refine ⟨productiveOfWitness (fun i j => P.nonneg (e i) (e j)) (w ∘ e) (fun i => hw (e i)) ?_⟩
  intro i
  rw [Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hAw (e i)

end Research

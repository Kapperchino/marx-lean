module
public import MarxLeanProof.Productivity
public import MarxLeanProof.Capabilities
@[expose] public section
set_option autoImplicit false

/-! # The support of the Leontief inverse (Proposition 4.3) -/
set_option linter.unusedSectionVars false

namespace Research
open Matrix Relation
open scoped BigOperators Research
variable {n q : Type*} [Fintype n] [DecidableEq n]

def support (A : Matrix n n ℝ) (i j : n) : Prop := 0 < A i j

lemma positive_mul_iff {A B : Matrix n n ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (i j : n) :
    0 < (A * B) i j ↔ ∃ k, 0 < A i k ∧ 0 < B k j := by
  rw [Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, pos_of_mul_pos_left hk (hB k j), pos_of_mul_pos_right hk (hA i k)⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, mul_pos hk hk'⟩

lemma path_of_power {A : Matrix n n ℝ} (hA : 0 ≤ A) (s : ℕ) (i j : n)
    (h : 0 < (A ^ s) i j) : ReflTransGen (support A) i j := by
  induction s generalizing j with
  | zero =>
    by_cases hij : i = j
    · subst j; exact .refl
    · simp [pow_zero, hij] at h
  | succ s ih =>
    rw [pow_succ, positive_mul_iff (pow_nonneg hA s) hA] at h
    obtain ⟨k, hk, hkj⟩ := h
    exact (ih k hk).tail hkj

lemma power_of_path {A : Matrix n n ℝ} (hA : 0 ≤ A) {i j : n}
    (h : ReflTransGen (support A) i j) : ∃ s : ℕ, 0 < (A ^ s) i j := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail j k hp he ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s+1, ?_⟩
    rw [pow_succ, positive_mul_iff (pow_nonneg hA s) hA]
    exact ⟨j, hs, he⟩

/-- An inverse entry is positive exactly when there is a supporting path. -/
theorem inverse_support {A : Matrix n n ℝ} (P : Productive A) (i j : n) :
    0 < P.N i j ↔ ReflTransGen (support A) i j := by
  have hs : HasSum (fun k : ℕ => (A ^ k) i j) (P.N i j) := by
    rw [P.neumann_series]
    exact Pi.hasSum.mp (Pi.hasSum.mp P.summable_powers.hasSum i) j
  constructor
  · intro hn
    by_contra hp
    have hz : ∀ k : ℕ, (A ^ k) i j = 0 := by
      intro k
      exact le_antisymm (le_of_not_gt (fun hk => hp (path_of_power P.nonneg k i j hk)))
        (pow_nonneg P.nonneg k i j)
    have hzero : P.N i j = 0 := by rw [← hs.tsum_eq]; simp only [hz, tsum_zero]
    linarith
  · intro hp
    obtain ⟨k, hk⟩ := power_of_path P.nonneg hp
    have hle := hs.summable.le_tsum k (fun s _ => pow_nonneg P.nonneg s i j)
    rw [hs.tsum_eq] at hle
    exact hk.trans_le hle

/-- Boolean labels embedded as zeros and ones in real arithmetic. -/
noncomputable def realLabels (D : q → n → Prop) : Matrix q n ℝ :=
  by
    classical
    exact fun k j => if D k j then 1 else 0

/-- Equation 4.7: the real inverse shortcut is exact for B=supp(A). -/
theorem label_inverse_support {A : Matrix n n ℝ} (P : Productive A)
    (D : q → n → Prop) (k : q) (j : n) :
    0 < (realLabels D * P.N) k j ↔ Capability.closure D (support A) k j := by
  classical
  rw [Matrix.mul_apply]
  have hd : ∀ i, 0 ≤ realLabels D k i := by intro i; simp only [realLabels]; split_ifs <;> norm_num
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hd i) (P.inverse_nonneg i j))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hdi : D k i
    · refine ⟨i, hdi, (inverse_support P i j).mp ?_⟩
      simpa [realLabels, hdi] using hi
    · simp [realLabels, hdi] at hi
  · rintro ⟨i, hdi, hp⟩
    exact ⟨i, by simpa [realLabels, hdi] using (inverse_support P i j).mpr hp⟩

/-- Extra declared technical edges can only enlarge the support annotation. -/
theorem label_support_le_declared {A : Matrix n n ℝ} (P : Productive A)
    (D : q → n → Prop) (B : n → n → Prop) (hB : ∀ i j, support A i j → B i j)
    (k : q) (j : n) :
    0 < (realLabels D * P.N) k j → Capability.closure D B k j := by
  intro h
  exact Capability.closure_mono (fun _ _ h => h) hB k j ((label_inverse_support P D k j).mp h)

end Research

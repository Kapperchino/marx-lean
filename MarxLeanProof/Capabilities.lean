module

public import Mathlib

@[expose] public section
set_option autoImplicit false

/-! # Boolean capability and missing-project closures (PDF §§4–5)
Relations are Boolean matrices represented by propositions. `mul` uses OR/AND,
not ordinary real multiplication. The executable finite iteration uses Finsets.
-/
namespace Research.Capability
open Relation
variable {n q : Type*}

/-- Boolean multiplication, with the PDF's upstream-to-downstream orientation. -/
def mul (D : q → n → Prop) (B : n → n → Prop) (k : q) (j : n) : Prop :=
  ∃ i, D k i ∧ B i j

/-- Reflexive transitive closure is the path semantics of B*. -/
def closure (D : q → n → Prop) (B : n → n → Prop) (k : q) (j : n) : Prop :=
  ∃ i, D k i ∧ ReflTransGen B i j

/-- Theorem 4.2: the reachability annotation is a fixed point. -/
theorem closure_fixed (D : q → n → Prop) (B : n → n → Prop) (k : q) (j : n) :
    closure D B k j ↔ D k j ∨ mul (closure D B) B k j := by
  constructor
  · rintro ⟨i, hi, hp⟩
    cases hp with
    | refl => exact Or.inl hi
    | @tail u v hp he => exact Or.inr ⟨u, ⟨i, hi, hp⟩, he⟩
  · rintro (hd | ⟨i, ⟨u, hu, hp⟩, he⟩)
    · exact ⟨j, hd, .refl⟩
    · exact ⟨u, hu, hp.tail he⟩

/-- Leastness, rather than uniqueness, is the essential condition in Theorem 4.2. -/
theorem closure_least (D : q → n → Prop) (B : n → n → Prop) (Z : q → n → Prop)
    (hz : ∀ k j, D k j ∨ mul Z B k j → Z k j) :
    ∀ k j, closure D B k j → Z k j := by
  rintro k j ⟨i, hi, hp⟩
  induction hp with
  | refl => exact hz k i (.inl hi)
  | @tail j l hp he ih => exact hz k l (.inr ⟨j, ih, he⟩)

theorem closure_mono {D D' : q → n → Prop} {B B' : n → n → Prop}
    (hD : ∀ k j, D k j → D' k j) (hB : ∀ i j, B i j → B' i j) :
    ∀ k j, closure D B k j → closure D' B' k j := by
  apply closure_least
  intro k j h
  apply (closure_fixed D' B' k j).mpr
  rcases h with hd | ⟨i, hi, hij⟩
  · exact .inl (hD k j hd)
  · exact .inr ⟨i, hi, hB i j hij⟩

/-- Zero labels and a self-loop graph have many fixed points (PDF p.7). -/
theorem fixed_not_unique (Z : q → n → Prop) (k : q) (j : n) :
    Z k j ↔ False ∨ mul Z (fun i j => i = j) k j := by
  simp [mul]

theorem empty_labels (B : n → n → Prop) (k : q) (j : n) :
    ¬ closure (fun _ _ => False) B k j := by simp [closure]

section Finite
variable [Fintype n] [DecidableEq n] (D : Finset n) (B : n → n → Prop) [DecidableRel B]

/-- One propagation round for a single capability label. -/
def step (X : Finset n) : Finset n := D ∪ Finset.univ.filter (fun j => ∃ i ∈ X, B i j)

def iterate : ℕ → Finset n
  | 0 => D
  | s + 1 => step D B (iterate s)

lemma mem_step (X : Finset n) (j : n) :
    j ∈ step D B X ↔ j ∈ D ∨ ∃ i ∈ X, B i j := by simp [step]

lemma step_mono {X Y : Finset n} (h : X ⊆ Y) : step D B X ⊆ step D B Y := by
  intro j hj
  rw [mem_step] at hj ⊢
  rcases hj with hd | ⟨i, hi, he⟩
  · exact .inl hd
  · exact .inr ⟨i, h hi, he⟩

lemma iterate_mono (s : ℕ) : iterate D B s ⊆ iterate D B (s + 1) := by
  induction s with
  | zero => exact Finset.subset_union_left
  | succ s ih => exact step_mono D B ih

lemma stable_next {s : ℕ} (h : iterate D B s = iterate D B (s + 1)) :
    iterate D B (s + 1) = iterate D B (s + 2) := by
  exact congrArg (step D B) h

lemma growth {s : ℕ} (h : iterate D B s ≠ iterate D B (s + 1)) :
    D.card + s + 1 ≤ (iterate D B (s + 1)).card := by
  induction s with
  | zero =>
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨iterate_mono D B 0, h⟩)
    simpa [iterate] using hc
  | succ s ih =>
    have hp : iterate D B s ≠ iterate D B (s + 1) := fun hh => h (stable_next D B hh)
    have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨iterate_mono D B (s+1), h⟩)
    have := ih hp
    omega

lemma iterate_empty (s : ℕ) : iterate (∅ : Finset n) B s = ∅ := by
  induction s with
  | zero => rfl
  | succ s ih => simp [iterate, step, ih]

/-- The exact n−1 iteration bound in Theorem 4.2, also valid when n=0. -/
theorem stabilizes :
    iterate D B (Fintype.card n - 1) = iterate D B (Fintype.card n) := by
  by_cases hd : D = ∅
  · subst D
    simp only [iterate_empty]
  · have hdpos : 0 < D.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hd)
    have hn : 0 < Fintype.card n := lt_of_lt_of_le hdpos (Finset.card_le_univ D)
    by_contra he
    have hs : iterate D B (Fintype.card n - 1) ≠
        iterate D B ((Fintype.card n - 1) + 1) := by simpa [Nat.sub_add_cancel hn] using he
    have hg := growth D B hs
    have hu := Finset.card_le_univ (iterate D B ((Fintype.card n - 1) + 1))
    omega

lemma bounded_sound (s : ℕ) (j : n) (hj : j ∈ iterate D B s) :
    closure (fun (_ : Unit) i => i ∈ D) B () j := by
  induction s generalizing j with
  | zero => exact ⟨j, hj, .refl⟩
  | succ s ih =>
    rw [iterate, mem_step] at hj
    apply (closure_fixed _ _ _ _).mpr
    rcases hj with hd | ⟨i, hi, he⟩
    · exact .inl hd
    · exact .inr ⟨i, ih i hi, he⟩

/-- The finite computation returns exactly D ⊙ B*, not just some fixed point. -/
theorem finite_eq_closure (j : n) :
    j ∈ iterate D B (Fintype.card n - 1) ↔ closure (fun (_ : Unit) i => i ∈ D) B () j := by
  constructor
  · exact bounded_sound D B _ j
  · apply closure_least (Z := fun (_ : Unit) l => l ∈ iterate D B (Fintype.card n - 1))
    intro _ l hl
    have hf : step D B (iterate D B (Fintype.card n - 1)) =
        iterate D B (Fintype.card n - 1) := by
      by_cases hn : Fintype.card n = 0
      · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
        exact Finset.eq_empty_of_isEmpty _ |>.trans (Finset.eq_empty_of_isEmpty _).symm
      · change iterate D B ((Fintype.card n - 1) + 1) = _
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
        exact (stabilizes D B).symm
    rw [← hf, mem_step]
    exact hl

end Finite

/-- Missing-project reachability: satisfied results stop traversal (5.3).
The graph is reversed because targets propagate to their upstream prerequisites. -/
def missing (P : n → n → Prop) (b τ : n → Prop) : n → Prop :=
  closure (fun (_ : Unit) i => b i ∧ τ i) (fun j i => b i ∧ P i j) ()

lemma missing_mask (P : n → n → Prop) (b τ : n → Prop) {j : n}
    (h : missing P b τ j) : b j := by
  rcases h with ⟨i, hi, hp⟩
  induction hp with
  | refl => exact hi.1
  | tail _ he _ => exact he.1

/-- Proposition 5.2's masked fixed-point equation. -/
theorem missing_fixed (P : n → n → Prop) (b τ : n → Prop) (j : n) :
    missing P b τ j ↔ b j ∧ (τ j ∨ ∃ i, P j i ∧ missing P b τ i) := by
  rw [missing, closure_fixed]
  simp only [mul]
  constructor
  · rintro (⟨hb, ht⟩ | ⟨i, hi, hb, he⟩)
    · exact ⟨hb, .inl ht⟩
    · exact ⟨hb, .inr ⟨i, he, hi⟩⟩
  · rintro ⟨hb, ht | ⟨i, he, hi⟩⟩
    · exact .inl ⟨hb, ht⟩
    · exact .inr ⟨i, hi, hb, he⟩

theorem missing_least (P : n → n → Prop) (b τ Z : n → Prop)
    (hZ : ∀ j, b j ∧ (τ j ∨ ∃ i, P j i ∧ Z i) → Z j) :
    ∀ j, missing P b τ j → Z j := by
  apply closure_least (Z := fun (_ : Unit) => Z)
  intro _ j h
  rcases h with ⟨hb, ht⟩ | ⟨i, hi, hb, he⟩
  · exact hZ j ⟨hb, .inl ht⟩
  · exact hZ j ⟨hb, .inr ⟨i, he, hi⟩⟩

/-- The masked project closure is also computable in at most |P|−1 rounds. -/
theorem finite_missing [Fintype n] [DecidableEq n]
    (P : n → n → Prop) [DecidableRel P] (b τ : n → Prop) [DecidablePred b] [DecidablePred τ]
    (j : n) :
    j ∈ iterate (Finset.univ.filter (fun i => b i ∧ τ i))
      (fun l i => b i ∧ P i l) (Fintype.card n - 1) ↔ missing P b τ j := by
  rw [finite_eq_closure]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, missing]

end Research.Capability

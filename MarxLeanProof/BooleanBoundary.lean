module
public import MarxLeanProof.Capabilities
@[expose] public section
set_option autoImplicit false

/-! # Exact Boolean boundary elimination (Appendix A.2)
Eliminating nodes contracts paths; it never turns all upstream labels into local
eligibility requirements. The proof works for empty blocks and cyclic graphs.
-/
namespace Research.Capability
open Relation
variable {n o q : Type*}

def externalGraph (B : (n ⊕ o) → (n ⊕ o) → Prop) (i j : o) := B (.inr i) (.inr j)
def effectiveGraph (B : (n ⊕ o) → (n ⊕ o) → Prop) (i j : n) : Prop :=
  B (.inl i) (.inl j) ∨ ∃ u v : o,
    B (.inl i) (.inr u) ∧ ReflTransGen (externalGraph B) u v ∧ B (.inr v) (.inl j)
def effectiveLabels (D : q → (n ⊕ o) → Prop) (B : (n ⊕ o) → (n ⊕ o) → Prop)
    (k : q) (j : n) : Prop :=
  D k (.inl j) ∨ ∃ u v : o,
    D k (.inr u) ∧ ReflTransGen (externalGraph B) u v ∧ B (.inr v) (.inl j)

lemma lift_external {B : (n ⊕ o) → (n ⊕ o) → Prop} {u v : o}
    (h : ReflTransGen (externalGraph B) u v) : ReflTransGen B (.inr u) (.inr v) := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact ih.tail he

lemma closure_extend {D : q → n → Prop} {B : n → n → Prop} {k : q} {i j : n}
    (hi : closure D B k i) (hp : ReflTransGen B i j) : closure D B k j := by
  obtain ⟨u, hu, hup⟩ := hi
  exact ⟨u, hu, hup.trans hp⟩

lemma effective_edge_path {B : (n ⊕ o) → (n ⊕ o) → Prop} {i j : n}
    (h : effectiveGraph B i j) : ReflTransGen B (.inl i) (.inl j) := by
  rcases h with h | ⟨u, v, hiu, huv, hvj⟩
  · exact ReflTransGen.single h
  · exact ((ReflTransGen.single hiu).trans (lift_external huv)).tail hvj

lemma effective_sound (D : q → (n ⊕ o) → Prop) (B : (n ⊕ o) → (n ⊕ o) → Prop) :
    ∀ k j, closure (effectiveLabels D B) (effectiveGraph B) k j → closure D B k (.inl j) := by
  apply closure_least
  intro k j hj
  rcases hj with (hd | ⟨u, v, hdu, huv, hvj⟩) | ⟨i, hi, he⟩
  · exact ⟨.inl j, hd, .refl⟩
  · exact ⟨.inr u, hdu, (lift_external huv).tail hvj⟩
  · exact closure_extend hi (effective_edge_path he)

/-- Equation A.7: exact equality of retained reachable labels. -/
theorem boundary_exact (D : q → (n ⊕ o) → Prop) (B : (n ⊕ o) → (n ⊕ o) → Prop)
    (k : q) (j : n) :
    closure D B k (.inl j) ↔ closure (effectiveLabels D B) (effectiveGraph B) k j := by
  let L := closure (effectiveLabels D B) (effectiveGraph B)
  let Z : q → (n ⊕ o) → Prop := fun k x => match x with
    | .inl j => L k j
    | .inr v => ∃ u : o, (D k (.inr u) ∨ ∃ i : n, L k i ∧ B (.inl i) (.inr u)) ∧
        ReflTransGen (externalGraph B) u v
  have hz : ∀ k x, D k x ∨ mul Z B k x → Z k x := by
    intro k x hx
    rcases hx with hd | ⟨y, hy, he⟩
    · cases x with
      | inl j => exact ⟨j, Or.inl hd, .refl⟩
      | inr v => exact ⟨v, Or.inl hd, .refl⟩
    · cases y with
      | inl i =>
        cases x with
        | inl j => exact (closure_fixed _ _ _ _).mpr (.inr ⟨i, hy, Or.inl he⟩)
        | inr v => exact ⟨v, Or.inr ⟨i, hy, he⟩, .refl⟩
      | inr v =>
        obtain ⟨u, hu, huv⟩ := hy
        cases x with
        | inl j =>
          rcases hu with hdu | ⟨i, hi, hiu⟩
          · exact ⟨j, Or.inr ⟨u, v, hdu, huv, he⟩, .refl⟩
          · exact (closure_fixed _ _ _ _).mpr (.inr ⟨i, hi, Or.inr ⟨u, v, hiu, huv, he⟩⟩)
        | inr w => exact ⟨u, hu, huv.tail he⟩
  exact ⟨closure_least D B Z hz k (.inl j), effective_sound D B k j⟩

end Research.Capability

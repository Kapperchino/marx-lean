module
public import MarxLeanProof.Simulator.Ledger
@[expose] public section
set_option autoImplicit false

/-! # v6.2 §§7.3,12,17: logical identity and safe event reordering
This is a conditional execution contract. It is not an implementation of CUDA,
SHA-256, a footprint extractor, a dependency frontier or a complete checkpoint.
-/
namespace Research.Simulator

inductive Phase where
  | opening | observe | propose | commit | workAndPay | provisionAndBuy
  | physicalClose | accountsAndDecisions | audit
  deriving DecidableEq, Repr

inductive NumericalProfile where
  | ref51 | gpuD1 | gpuF1 | reducedP0
  deriving DecidableEq, Repr

/-- Subphases and persistent IDs supply the within-day order. -/
structure EventKey where
  day : ℕ
  phase : Fin 9
  subphase : ℕ
  priority : ℕ
  persistentID : ℕ
  deriving DecidableEq, Repr

structure DrawKey where
  seed : ℕ
  day : ℕ
  domain : String
  persistentID : ℕ
  drawIndex : ℕ
  deriving DecidableEq, Repr

/-- Domain: denominator > 0 and numerator ≤ denominator. Draws lie below 2^bits.
Generalized bit width allows the PDF's two-bit counterexample; production uses 128. -/
def drawThreshold (bits numerator denominator : ℕ) : ℕ := 2 ^ bits * numerator / denominator
def drawSuccess (bits numerator denominator draw : ℕ) : Prop :=
  draw < drawThreshold bits numerator denominator

theorem draw_zero (bits denominator draw : ℕ) : ¬ drawSuccess bits 0 denominator draw := by
  simp [drawSuccess, drawThreshold]

/-- Threshold 2^bits needs a separate tag in a fixed-width implementation. -/
theorem draw_one (bits denominator draw : ℕ) (hd : 0 < denominator) (hu : draw < 2 ^ bits) :
    drawSuccess bits denominator denominator draw := by
  simpa [drawSuccess, drawThreshold, Nat.ne_of_gt hd] using hu

/-- Discovery, mastery, permission and installed adoption are separate gates. -/
structure Readiness where
  discovered : Prop
  mastered : Prop
  permitted : Prop
  adopted : Prop
  resources : Prop
  time : Prop
  authority : Prop

def Readiness.Executable (r : Readiness) : Prop :=
  r.discovered ∧ r.mastered ∧ r.permitted ∧ r.adopted ∧ r.resources ∧ r.time ∧ r.authority

/-- All mutable read dependencies, including rejection/eligibility predicates,
must be in the footprint. Unchanged writes outside it and local reads are proofs,
not assumptions silently supplied by the scheduler. -/
structure LocalEvent (resource value : Type*) where
  footprint : Set resource
  step : (resource → value) → resource → value
  accepted : (resource → value) → Bool
  frame : ∀ s i, i ∉ footprint → step s i = s i
  localState : ∀ s t, Set.EqOn s t footprint → Set.EqOn (step s) (step t) footprint
  localDecision : ∀ s t, Set.EqOn s t footprint → accepted s = accepted t

variable {resource value : Type*}

theorem Bundle.feasible_local (e : Bundle resource) (footprint : Set resource)
    (outside : ∀ i ∉ footprint, e.debit i = 0)
    (guard : ∀ s t, Set.EqOn s t footprint → (e.authorized s ↔ e.authorized t))
    (s t : resource → ℕ) (h : Set.EqOn s t footprint) : e.Feasible s ↔ e.Feasible t := by
  have forward (s t : resource → ℕ) (heq : Set.EqOn s t footprint)
      (hs : e.Feasible s) : e.Feasible t := by
    refine ⟨(guard s t heq).mp hs.1, ?_⟩
    intro i
    by_cases hi : i ∈ footprint
    · simpa only [heq hi] using hs.2 i
    · rw [outside i hi]; exact Nat.zero_le _
  exact ⟨forward s t h, forward t s h.symm⟩

/-- Concrete ledger bundles satisfy the scheduling contract once their guard
reads and all debit/credit coordinates are contained in the declared footprint. -/
noncomputable def Bundle.toLocalEvent (e : Bundle resource) (footprint : Set resource)
    (outside : ∀ i ∉ footprint, e.debit i = 0 ∧ e.credit i = 0)
    (guard : ∀ s t, Set.EqOn s t footprint → (e.authorized s ↔ e.authorized t)) :
    LocalEvent resource ℕ := by
  classical
  have localFeasible := e.feasible_local footprint (fun i hi => (outside i hi).1) guard
  exact {
    footprint := footprint
    step := e.commit
    accepted := fun s => decide (e.Feasible s)
    frame := by
      intro s i hi
      simp only [Bundle.commit]
      split_ifs <;> simp [(outside i hi).1, (outside i hi).2]
    localState := by
      intro s t heq i hi
      have hf := localFeasible s t heq
      simp only [Bundle.commit]
      by_cases hs : e.Feasible s
      · simp [hs, hf.mp hs, heq hi]
      · have ht : ¬ e.Feasible t := fun ht => hs (hf.mpr ht)
        simp [hs, ht, heq hi]
    localDecision := by
      intro s t heq
      simp [localFeasible s t heq]
  }

theorem LocalEvent.eqOn_disjoint (e f : LocalEvent resource value)
    (h : Disjoint e.footprint f.footprint) (s : resource → value) :
    Set.EqOn (f.step s) s e.footprint := by
  intro i hi
  exact f.frame s i (fun hf => Set.disjoint_left.mp h hi hf)

/-- Independent events preserve each other's accept/reject decisions. -/
theorem LocalEvent.decision_commutes (e f : LocalEvent resource value)
    (h : Disjoint e.footprint f.footprint) (s : resource → value) :
    e.accepted (f.step s) = e.accepted s :=
  e.localDecision _ _ (e.eqOn_disjoint f h s)

/-- The local diamond used by the serial/frontier equivalence argument in §17.2. -/
theorem LocalEvent.commute (e f : LocalEvent resource value)
    (h : Disjoint e.footprint f.footprint) (s : resource → value) :
    e.step (f.step s) = f.step (e.step s) := by
  funext i
  by_cases he : i ∈ e.footprint
  · have hf : i ∉ f.footprint := fun hf => Set.disjoint_left.mp h he hf
    rw [f.frame _ i hf]
    exact e.localState _ _ (e.eqOn_disjoint f h s) he
  · rw [e.frame _ i he]
    by_cases hf : i ∈ f.footprint
    · exact (f.localState _ _ (f.eqOn_disjoint e h.symm s) hf).symm
    · rw [f.frame _ i hf, f.frame _ i hf, e.frame _ i he]

def execute (events : List (LocalEvent resource value)) (s : resource → value) : resource → value :=
  events.foldl (fun state e => e.step state) s

/-- Only independent adjacent swaps are permitted, within a fixed observation
boundary with fixed handlers, payloads and arithmetic. -/
inductive SafeReorder : List (LocalEvent resource value) → List (LocalEvent resource value) → Prop
  | refl (xs) : SafeReorder xs xs
  | swap (e f : LocalEvent resource value) (xs) (h : Disjoint e.footprint f.footprint) :
      SafeReorder (e :: f :: xs) (f :: e :: xs)
  | cons (e) {xs ys} : SafeReorder xs ys → SafeReorder (e :: xs) (e :: ys)
  | trans {xs ys zs} : SafeReorder xs ys → SafeReorder ys zs → SafeReorder xs zs

theorem safeReorder_execute {xs ys : List (LocalEvent resource value)} (h : SafeReorder xs ys)
    (s : resource → value) : execute xs s = execute ys s := by
  induction h generalizing s with
  | refl => rfl
  | swap e f xs hd => simp only [execute, List.foldl_cons, e.commute f hd]
  | cons e h ih => exact ih (e.step s)
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ s).trans (ih₂ s)

/-- Edges that strictly increase canonical indices cannot form a nonempty cycle. -/
theorem forward_dependencies_acyclic {event : Type*} (rank : event → ℕ)
    (edge : event → event → Prop) (forward : ∀ a b, edge a b → rank a < rank b)
    (a : event) : ¬ Relation.TransGen edge a a := by
  intro cycle
  have strict : ∀ {b c}, Relation.TransGen edge b c → rank b < rank c := by
    intro b c path
    induction path with
    | single h => exact forward _ _ h
    | tail _ h ih => exact ih.trans (forward _ _ h)
  exact (lt_irrefl (rank a)) (strict cycle)

end Research.Simulator

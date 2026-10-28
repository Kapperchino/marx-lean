# Unified Economic Simulator v6.2 — Lean formalization

This project formalizes the mathematical contracts in
[`Unified_Economic_Simulator_Formal_Model_v6_2_Explained_GPU.pdf`](Unified_Economic_Simulator_Formal_Model_v6_2_Explained_GPU.pdf)
(27 October 2026), using **Lean 4.35.0** and **Mathlib v4.35.0**. The new
`Research.Simulator` namespace extends the existing `Research` library without
changing its theorems. The source PDF is unchanged.

The update covers exact event accounting, production packets, fractional claims,
sparse analytical equations, certified error bounds, policy formulas, dated
financing, household support and a conditional proof of safe event reordering.
It is a Lean specification and proof library, not a running economic simulator or
a GPU implementation. The correspondence table below distinguishes definitions,
proved properties and implementation obligations.

The earlier research-accounting exposition remains available as
[`research_context_mathematical_paper.pdf`](research_context_mathematical_paper.pdf),
with consolidated theorem statements, prose proofs, equations, and small examples. Its editable
LaTeX source is
[`research_context_mathematical_paper.tex`](research_context_mathematical_paper.tex).
The local macOS exporter is `python3 scripts/export_paper.py`; it uses Node,
the installed VS Code KaTeX bundle, and Swift/CoreText. The `.tex` source can
also be compiled by a standard LaTeX installation.

```sh
lake build
```

The default target imports all proof modules, the exact examples, and the axiom
audit. For a new checkout with Elan installed, run `lake exe cache get` before
the build to fetch Mathlib's compiled artifacts. Dependencies are pinned in
`lean-toolchain` and `lake-manifest.json`.

On macOS, `python3 scripts/export_pdf.py` verifies and exports the complete
current library to `unified_economic_simulator_v6_2_lean_proof.pdf`, including
the nested simulator modules, source hashes and the coverage guide.

Use the library with:

```lean
import MarxLeanProof

open Research
open scoped Research

#check Research.unified_unique
#check Research.equalResidual_iff_spectral
#check Research.Capability.finite_eq_closure
#check Research.weighted_labor_truncation
#check Research.Simulator.coupled_productive_iff
#check Research.Simulator.planValue_eq_hours
#check Research.Simulator.weighted_residual_bound
#check Research.Simulator.safeReorder_execute
```

`unified_unique` proves uniqueness of the occupational account and the normalized
conversion pair together. `equalResidual_iff_spectral` proves that the conversion
pair exists uniquely exactly when the nonnegative reproduction matrix has
spectral radius below one.

## Correspondence with v6.2

Names in this table are in `Research.Simulator` unless otherwise qualified.
Equation numbers refer to the supplied 37-page reader's edition. Its S9–S11
labels retain the numbering from v6.1.

| PDF sections / equations | Definitions and proved properties |
| --- | --- |
| §2.2; 2.1: labeled analytical comparators | [Analytics.lean](MarxLeanProof/Simulator/Analytics.lean): `surplusComparator` and `comparatorRate`; the rate is unavailable for a nonpositive requirement. Population, classification, time period and comparator convention remain supplied context. |
| §§3, 5; 5.1–5.3: units, complete events and payments | [Ledger.lean](MarxLeanProof/Simulator/Ledger.lean): `Coordinate`, positive rational `Quantum`, signed `post`; `post_conserves` for balanced instrument legs; `Bundle.Feasible` checks grouped gross debits and a scenario-supplied authorization predicate; `Bundle.accepted`, `.rejected`, `resolve_rejected`; separate cross-bank deposit and reserve conservation. |
| §6.1; 6.2–6.3: exact production packets | [Packets.lean](MarxLeanProof/Simulator/Packets.lean): denominator LCM, positivity, divisibility/minimal-common-multiple property and `packetTicks_exact`; `le_packetCount_iff` proves the packet count is the greatest feasible count under the plan and every listed gross resource bound, including zero-input and empty-resource cases. |
| §6.2; 6.4–6.6: fractional obligations | [Ledger.lean](MarxLeanProof/Simulator/Ledger.lean): `Claim` has a positive denominator; decomposition, accrual, permitted settlement, `Claim.settle_conserves` and `.settle_remainder`. The cash transfer is a separate accepted event. |
| §7.1; 7.1–7.3: bounded policies, grid quotes, observations | [Policies.lean](MarxLeanProof/Simulator/Policies.lean): clipping, affine blending, missing-observation branch, exact rational quote grids; `quoteTicks_legal` proves floor/cap compliance. Empty legal intervals return `none`. |
| §§7.2–7.3; 7.4: nonlinear policies and keyed draws | [Policies.lean](MarxLeanProof/Simulator/Policies.lean): real hazard/sigmoid definitions and hazard bounds. [Execution.lean](MarxLeanProof/Simulator/Execution.lean): logical `DrawKey`, exact floored threshold, zero/one endpoint proofs. SHA-256 serialization and GPU-D1 lookup tables are implementation obligations. |
| §8; 8.1–8.4: goods requirements | [Analytics.lean](MarxLeanProof/Simulator/Analytics.lean): certificate-requiring `solve`, fixed-point identity, uniqueness and nonnegativity; existing `Research.Productive.scalar_fixed`, `.scalar_unique` prove the external-weight goods equation. |
| §9; 9.1–9.5: optional occupational closure | [Analytics.lean](MarxLeanProof/Simulator/Analytics.lean): per-hour goods/training formulas, `coupledOperator`, simultaneous `coupledStep`, equivalence with the four block products, `coupled_reduction`, `coupled_productive_iff`, `coupled_spectral_iff`, `coupled_beta_ge_one`, and `normalized_coupled`. Goods admissibility is retained. Existing conversion proofs provide the unique positive normalized weights. |
| §10; 10.1–10.4: research attempts and plans | [Analytics.lean](MarxLeanProof/Simulator/Analytics.lean): `researchValues`, two-dot-product `planValue`, and `planValue_eq_hours`. Existing inventory and historical research identities remain in [Accounting.lean](MarxLeanProof/Accounting.lean); historical discovery costs are not added to subsequent product requirements. |
| §11; 11.1–11.4: certified accuracy and unavailable results | [Solver.lean](MarxLeanProof/Simulator/Solver.lean): `weightedMax`, `weighted_residual_bound`, `productiveOfContraction`, and `normalization_bounds`, including zero goods-value lower bounds. `Diagnostic` distinguishes missing data, inapplicability, inadmissibility and unresolved accuracy; `cachedValue` rejects a mismatched context version. |
| §12; 12.1–12.2: capability and missing-project closure | Existing `Research.Capability.finite_eq_closure`, `.finite_missing` and related support/boundary proofs are retained. [Execution.lean](MarxLeanProof/Simulator/Execution.lean) separately represents discovery, mastery, permission, adoption, resources, time and authority in `Readiness.Executable`. Closure alone is not a readiness proof. |
| §13; S9.1–S9.4: households and work capacity | [Policies.lean](MarxLeanProof/Simulator/Policies.lean): need deficits with a zero-need branch and proved bounds, participation/time availability, health and fatigue formulas. Inputs represent delivered services and executed activities. |
| §14; S9.5–S9.10: firms, equipment, natural stocks, research | [Policies.lean](MarxLeanProof/Simulator/Policies.lean): demand smoothing, proposed starts, machine capacity/condition, nonincreasing lifetime service, renewable-stock bounds, price candidates, research effort scale, success hazard and exposure. Zero research effort has zero success probability. |
| §15; S10.1–S10.9: payroll and bargaining | [Policies.lean](MarxLeanProof/Simulator/Policies.lean): rational hinge taxes, net increments and their cross-employer telescoping identity, affine bracket inverse with correctness proof, directional wage grids, employer ceiling, household anchor/refusal factor, bargaining weight and second offer. The selected bracket and positive marginal slope remain explicit preconditions of inversion. |
| §16; S11.1–S11.5: finance and collective support | [Finance.lean](MarxLeanProof/Simulator/Finance.lean): lending caps with a liquidity bound, prefix-based `openingNeed` and exact cushion equivalence, financing gap, replacement earmark, rent bid and discounted flows; household support with individual bounds and `supportGrant_total = min treasury totalNeed`. [Policies.lean](MarxLeanProof/Simulator/Policies.lean) defines the strike score and proves its stated range. Consent and authorization remain separate event gates. |
| §17.2: deterministic execution | [Execution.lean](MarxLeanProof/Simulator/Execution.lean): `Bundle.toLocalEvent` connects ledger bundles to complete-footprint `LocalEvent`; independent states commute and accept/reject decisions remain unchanged; `safeReorder_execute` preserves the serial state under independent adjacent swaps; forward canonical dependency edges are acyclic. |
| §17.3; 17.1: divisible-pool shortcut | [Finance.lean](MarxLeanProof/Simulator/Finance.lean): serial partial fills, remaining-capacity identity, and `prefixFills_total`. This API is for a divisible pool with prevalidated demands, no inflows and no private failure gates; indivisible counterexamples exercise `resolve` instead. |
| §§17.4–18: runtime profiles, caches, evidence | Profile/phase/key and context-version types record specification distinctions. Device data layout, bounded machine arithmetic, policy tables, scheduler construction, checkpoint completeness, CPU/GPU replay, performance and economic calibration are not proved by this library. |

### Domains and execution boundary

Ledger ticks use unbounded `ℕ`/`ℤ`, and fractional obligations and quote/payroll
examples use exact `ℚ`. Analytical equations and continuous policies use `ℝ`.
No machine-width overflow, floating-point roundoff or backend determinism is
inferred from these types. A backend must check intermediate arithmetic and
implement its declared rounding and table versions.

`Bundle.commit` checks affordability **before** subtracting gross inputs. The
accepted-event theorem equates its natural-number update with signed integer
posting, so subtraction does not silently discard a shortage. Credits cannot fund
the same event's initial debit. The abstract authorization predicate must include
all relevant rights, consent, protected versions, timing and other scenario gates.
Reservation, release and delayed production stages require their own dated bundles.

Policy functions are mathematical formulas with the PDF's stated domains, not
validators for arbitrary scenario inputs. In particular: lifetimes and research
effort scales are positive; weights/health/fatigue lie in their declared intervals;
wage and tax inversion require valid brackets, positive grid size and payable
hours; household anchors require positive participating-adult count and normal
day; lending requires positive term, minimum capital ratio and risk weight.
Theorems expose the hypotheses used. Only quote availability and the explicitly
defined missing/zero branches are handled inside their respective functions.

The scheduler theorem requires proofs of complete read footprints and unchanged
state outside each footprint. A concrete dependency-frontier implementation must
establish that its event order is a `SafeReorder` of the canonical order. It must
also retain observation boundaries, fixed payloads/handlers/arithmetic and logical
IDs. The proof does not certify an arbitrary parallel schedule or a GPU runtime.

The retained v6.0/v5.1 attachments supply additional scenario rules; this update
does not claim to implement every inherited institutional handler or initializer.
It follows v6.2's own distinction between mathematical identities, exact-account
contracts, and implementation-level replay evidence.

### Exact v6.2 examples

[Simulator/Examples.lean](MarxLeanProof/Simulator/Examples.lean) checks the settled
wage/purchase sequence; rejected-first-buyer fallback; cross-bank balances; gross
versus net resource requirements; six-unit packets and the two-packet capacity;
fractional thirds; legal/empty quote grids; the two-bit floored-draw counterexample;
grain/bread values, raw coupled solution, research cost 6 and total 12; weighted
residual bound 0.1; household deficit 0.25; tax/wage figures; funding needs 8 and 11;
household grants `(1,2,3)`; divisible fills `(2,3,0)`; and indivisible jobs `(6,4)`
against capacity 5. The default build includes all of these and audits their
transitive axioms alongside the legacy proofs.

Five additional review regressions use independently chosen inputs to check
simultaneous updates away from a fixed point, asymmetric two-occupation closure
and normalization, an operator certificate that fails for its transpose, and a
valid goods account whose optional occupational closure is inadmissible. These
are distinguished from the PDF's teaching fixtures in the source.

v6.2 source SHA-256:
`081ae1a1b32535cde678c5c68a4e700ab5003598d30dc23499ba4e31bc9f2d56`.

## Correspondence with the simplified mathematical paper

The shorter paper groups results by the argument they share. Its principal
statements correspond to the following existing proofs; the Lean library also
retains the full numerical examples from the original paper.

| Mathematical paper | Formal results |
| --- | --- |
| Theorem 1.1 and Corollary 1.2: productivity and accounts | `spectral_iff_productive`, `productive_iff_summable`, `productive_iff_witness`, `productive_iff_reproduction`; `Productive.labor_existsUnique`, `.labor_series`, `.scalar_existsUnique`; `project_fresh` |
| Theorem 2.1: closure and support | `Capability.closure_fixed`, `.closure_least`, `.finite_eq_closure`; `inverse_support`, `label_inverse_support`, `label_support_le_declared` |
| Proposition 2.2: missing projects and terminal outputs | `Capability.missing_fixed`, `.missing_least`, `.finite_missing`; `Productive.append`, `terminal_labor`, `copying_limit` |
| Proposition 3.1: inventories | `inventory_reconciliation`, `inventory_horizon` |
| Theorem 4.1 and Proposition 4.2: normalized weights and augmented system | `equalResidual_iff_spectral`, `Conversion.existsUnique`, `.change_reference`, `.equal_column_sums`; `augmented_inverse`, `augmented_spectral_iff`, `unified_unique` |
| Theorem 5.1: boundary reduction | `Productive.external`, `.eliminate`; `boundary_labor_solution`, `boundary_demand_labor`, `boundary_conversion`; `Capability.boundary_exact` |
| Proposition 5.2: units | `labor_change_units`, `demand_change_units`, `support_change_units`, `reproduction_change_physical_units`, `lifetime_unit_covariance`, `residual_change_labor_units`, `reference_rebase` |
| Propositions 6.1–6.2: changes and error bounds | `labor_difference`, `labor_monotone`, `labor_hasDerivAt`, `coefficient_hasDerivAt`, `beta_hasDerivAt`, `normalized_derivative`, `values_derivative`, `weighted_labor_truncation`, `residual_error_bound`, `ratio_bounds` |

## Legacy correspondence with the audited research PDF

Names below are in `Research` unless an additional namespace is shown.

| PDF result | Lean result and location |
| --- | --- |
| Context, project eligibility, reusable outcomes, valuation record (2.1, 2.2, 4.4, 5.2) | `Context`, `Project.Eligible`, `grantResults_*`, `valuation` in [Model.lean](MarxLeanProof/Model.lean) |
| Theorem 3.1: all five productivity criteria | `spectral_iff_summable`, `spectral_iff_productive` in [Spectral.lean](MarxLeanProof/Spectral.lean); `productive_iff_witness`, `productive_iff_summable`, `productive_iff_reproduction` in [Productivity.lean](MarxLeanProof/Productivity.lean) |
| Theorem 3.2: unique occupational account, Neumann layers, final demand | `Productive.labor_existsUnique`, `.labor_nonneg`, `.final_demand`, `.unit_requirement` in [Basic.lean](MarxLeanProof/Basic.lean); `.labor_series` in [Productivity.lean](MarxLeanProof/Productivity.lean) |
| Proposition 3.4: supplied scalar weights and unique scalar account | `Productive.scalar_fixed`, `.scalar_unique`, `.scalar_existsUnique` in [Basic.lean](MarxLeanProof/Basic.lean) |
| Proposition 3.5: monotonicity and finite changes | `productiveOfLe` in [Productivity.lean](MarxLeanProof/Productivity.lean); `labor_monotone`, `labor_difference` in [Accounting.lean](MarxLeanProof/Accounting.lean) |
| Proposition 3.5: differential and coefficient identities, including existence | `MatrixDeriv.leontiefInverse`, `labor_hasDerivAt`, `coefficient_hasDerivAt` in [Sensitivity.lean](MarxLeanProof/Sensitivity.lean) |
| Proposition 3.6: physical units | `Productive.changeUnits`, `labor_change_units`, `demand_change_units`, `support_change_units` in [Units.lean](MarxLeanProof/Units.lean); `spectralRadius_change_units` in [Spectral.lean](MarxLeanProof/Spectral.lean) |
| Theorem 4.2: Boolean least fixed point and finite termination | `Capability.closure_fixed`, `.closure_least`, `.stabilizes`, `.finite_eq_closure` in [Capabilities.lean](MarxLeanProof/Capabilities.lean) |
| Proposition 4.3: numerical inverse and Boolean support | `inverse_support`, `label_inverse_support`, `label_support_le_declared` in [Support.lean](MarxLeanProof/Support.lean) |
| Proposition 5.1: fresh project requirements | `project_fresh`, `project_nonneg` in [Accounting.lean](MarxLeanProof/Accounting.lean) |
| Proposition 5.2: masked missing-project closure | `Capability.missing_fixed`, `.missing_least`, `.finite_missing` in [Capabilities.lean](MarxLeanProof/Capabilities.lean) |
| Theorem 6.1 and Corollary 6.2: terminal activities and copying limit | `Productive.append`, `terminal_labor` in [Blocks.lean](MarxLeanProof/Blocks.lean); `copying_limit` in [Sensitivity.lean](MarxLeanProof/Sensitivity.lean) |
| Proposition 7.1: inventories and chronological reconciliation | `inventory_reconciliation`, `inventory_telescope`, `inventory_horizon` in [Accounting.lean](MarxLeanProof/Accounting.lean) |
| Proposition 9.1: weighted truncation bound | `witness_scaled_norm_lt_one`, `labor_truncation`, `weighted_labor_truncation` in [Truncation.lean](MarxLeanProof/Truncation.lean) |
| Proposition A.1: numeric boundary elimination with feedback | `Productive.external`, `.eliminate` in [Blocks.lean](MarxLeanProof/Blocks.lean); `boundary_labor_solution`, `boundary_demand_labor` in [Accounting.lean](MarxLeanProof/Accounting.lean) |
| Proposition A.2: Boolean boundary elimination | `Capability.boundary_exact` in [BooleanBoundary.lean](MarxLeanProof/BooleanBoundary.lean) |
| Theorem C.2: positive normalized conversion, both directions | `equalResidual_iff_spectral` in [Theorems.lean](MarxLeanProof/Theorems.lean); `Conversion.satisfies`, `.unique`, `.existsUnique` in [Conversion.lean](MarxLeanProof/Conversion.lean) |
| Definition C.3 and Proposition C.4: ratios, references, equal column sums | `Conversion.ratio`, `.change_reference`, `.equal_column_sums` in [Conversion.lean](MarxLeanProof/Conversion.lean) |
| Proposition C.5: augmented system and explicit inverse | `augmented_inverse`, `augmented_equations` in [Blocks.lean](MarxLeanProof/Blocks.lean); `augmented_spectral_iff` in [Theorems.lean](MarxLeanProof/Theorems.lean) |
| Proposition C.6: physical units and reproduction inputs | `reproduction_change_physical_units` in [Units.lean](MarxLeanProof/Units.lean) |
| Proposition C.7: conversion sensitivity | `reproduction_derivative`, `beta_hasDerivAt`, `normalized_derivative`, `values_derivative` in [Sensitivity.lean](MarxLeanProof/Sensitivity.lean); `beta_monotone` in [Theorems.lean](MarxLeanProof/Theorems.lean) |
| Proposition C.8: conversion-preserving boundary reduction | `boundary_conversion` in [Accounting.lean](MarxLeanProof/Accounting.lean) |
| Proposition C.9: occupational time units and rebasing | `lifetime_unit_covariance`, `residual_change_labor_units`, `values_change_labor_units`, `labor_unit_ratio`, `reference_rebase` in [Units.lean](MarxLeanProof/Units.lean) |
| C.12: residual and ratio error bounds | `residual_error`, `ratio_bounds` in [Conversion.lean](MarxLeanProof/Conversion.lean); `residual_error_bound` in [Sensitivity.lean](MarxLeanProof/Sensitivity.lean) |
| Unified specification C.19 | `unified_unique` in [Model.lean](MarxLeanProof/Model.lean), together with the definitions of `valuation`, `reproductionMatrix`, `Conversion.beta`, `.alpha`, and `projectLabor` |
| Worked examples and interpretation counterexamples | [Examples.lean](MarxLeanProof/Examples.lean) |

## Representation and assumptions

- Matrices have finite index types and real entries. `A i j` is input `i` per
  output `j`. Matrix inequalities use **entrywise order**, enabled by
  `open scoped Research`; Mathlib's positive-semidefinite matrix order is not the
  order used in this paper.
- `Productive A` contains nonnegativity and a nonnegative two-sided inverse of
  `1 - A`. `Productive.inverse_eq` identifies it with the usual matrix inverse.
  The spectral, Neumann-series, positive-witness, and reproduction criteria are
  proved equivalent; the certificate does not assume the labor conclusions.
- `SpectralProductive` uses the complexification of the real matrix, so it
  includes non-real eigenvalues. The spectral equivalence results use the
  paper's nonempty ordinary dimension. Most algebraic and Boolean results also
  allow empty index types, including zero capability labels and empty boundary
  blocks.
- Boolean matrices are predicates and multiplication is existential OR/AND.
  `Capability.iterate` is a finite-set computation, proved to return the least
  closure after at most `card n - 1` propagation rounds. Missing-project edges
  are reversed and masked to stop at already satisfied results.
- `EqualResidual` is an explicit hypothesis/predicate, never a Lean axiom.
  Nonnegative reproduction data alone do not assert that equal residuals are
  the correct economic convention. `Γinv` in the low-level formulas denotes
  the supplied inverse lifetime matrix; positive diagonal lifetime inverses
  can be constructed with `inverseUnitMatrix` and its inverse lemmas.
- `labor_hasDerivAt` and `beta_hasDerivAt` construct the derivatives of the
  inverse-based solution curves from coefficient derivatives and productivity
  at the evaluation point. `coefficient_hasDerivAt` specializes this to a single
  matrix entry. The older `labor_derivative` and `beta_derivative` also support
  arbitrary differentiable solution curves satisfying the balance equations.
  These results concern fixed coordinates and the smooth algebraic extension
  of the inverse formula; they do not assert differentiability across catalogue
  changes or changes of the feasibility regime.
- Inventory identities permit signed stock adjustments and real attempt
  quantities, so they also apply when actual attempts are natural numbers
  embedded in the reals. `inventory_horizon` fixes `A,H` but permits varying
  project input and direct-labor matrices.
- Truncation norms are the maximum absolute row-sum operator norm. The
  unweighted lemma counts retained terms; the weighted lemma uses the PDF's
  `k + 1` terms and exponent exactly.

The formalization does not prove empirical validity, interpretive claims about
Marx, feasible scheduling from endpoint balances, project success, or the
correctness of a supplied dependency graph. Algorithmic operation-count claims
and the optimized strongly-connected-component implementation are not
formalized; the finite closure algorithm and its termination bound are.

## Verification

[Examples.lean](MarxLeanProof/Examples.lean) checks the physical and software
examples, occupational weights, the material diamond, shared prerequisites,
the six-output conversion example (`11/8`, `117/160`, `181/4`), boundary-deletion
and occupational-unit counterexamples, and the identification and inventory
cautions. Arithmetic uses exact real/rational expressions and kernel-checked
tactics. Boolean examples use `decide`.

[Audit.lean](MarxLeanProof/Audit.lean) examines transitive axiom dependencies of
imported project declarations, including generated declarations. The build
fails if a dependency is anything other than `propext`, `Classical.choice`, or
`Quot.sound`. There are no proof placeholders, added axioms, or native-evaluation
proof oracles. To rerun the audit even if Lake considers the build current:

```sh
lake env lean MarxLeanProof/Audit.lean
```

To rebuild all project proofs while retaining the Mathlib cache:

```sh
lake clean marx-lean-proof
lake --wfail build
```

The review also tested the audit command against isolated imported fixtures:
an ordinary proof passed, while an additional axiom and a proof placeholder
were each rejected. The fixtures are outside the proof library. A concrete
off-diagonal coefficient perturbation checked the new derivative theorem's
orientation without assuming a derivative of the solution.

The legacy research PDF's separate 135-check Python bundle is not the Lean proof suite and is
not required by this project. Compilation checks the general proofs as well as
the Lean examples.

Legacy audited research source PDF SHA-256 (retained provenance):
`dbe34d3afe1fb2f27c19cba55af498ab9bc8f7546fe73254e69b37160af94446`.

# Research as Production Context — Lean formalization

This project formalizes the conditional mathematical results in
[`research_context_formula_audited.pdf`](research_context_formula_audited.pdf),
including its audited conversion appendix, using **Lean 4.35.0** and
**Mathlib v4.35.0**. The original PDF is unchanged.

The conventional mathematical exposition is
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

Use the library with:

```lean
import MarxLeanProof

open Research
open scoped Research

#check Research.unified_unique
#check Research.equalResidual_iff_spectral
#check Research.Capability.finite_eq_closure
#check Research.weighted_labor_truncation
```

`unified_unique` proves uniqueness of the occupational account and the normalized
conversion pair together. `equalResidual_iff_spectral` proves that the conversion
pair exists uniquely exactly when the nonnegative reproduction matrix has
spectral radius below one.

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

## Correspondence with the supplied audited PDF

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

The PDF's separate 135-check Python bundle is not the Lean proof suite and is
not required by this project. Compilation checks the general proofs as well as
the Lean examples.

Source PDF SHA-256:
`dbe34d3afe1fb2f27c19cba55af498ab9bc8f7546fe73254e69b37160af94446`.

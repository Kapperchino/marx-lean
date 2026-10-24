module
public import MarxLeanProof.Model
public import MarxLeanProof.BooleanBoundary
public import MarxLeanProof.Sensitivity
public import MarxLeanProof.Truncation
public import MarxLeanProof.Examples
public import Lean.Util.CollectAxioms

/-! This command runs during compilation and inspects transitive dependencies.
Only Lean's usual classical foundations are permitted; a proof placeholder or
an additional assumption declared as an axiom makes the build fail.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => (`MarxLeanProof).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if fromProject then
      checked := checked + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  if checked == 0 then
    throwError "No project declarations were found; check the audit imports"
  logInfo m!"Axiom audit passed: {checked} project declarations; only propext, Classical.choice and Quot.sound are permitted."

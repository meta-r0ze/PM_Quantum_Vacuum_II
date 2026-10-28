import PMAction
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => (`PMAction).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if fromProject || (`PMAction).isPrefixOf name || (`_private.PMAction).isPrefixOf name then
      let deps ← Lean.collectAxioms name
      for dep in deps do
        unless dep == ``propext || dep == ``Classical.choice || dep == ``Quot.sound do
          throwError "Unapproved axiom {dep} in {name}"
      checked := checked + 1
  if checked == 0 then throwError "No project declarations found"
  logInfo m!"Strict axiom audit passed: {checked} PMAction declarations"

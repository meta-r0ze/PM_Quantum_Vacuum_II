import PMAction
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.allImportedModuleNames do
    for downstream in [`PMConstants, `PMFlavor, `PMElementaryParticles, `PMCosmology] do
      if downstream.isPrefixOf name then
        throwError "Downstream dependency {name} in Paper II"
  logInfo "Dependency audit passed: no Paper III–VI imports in Paper II"

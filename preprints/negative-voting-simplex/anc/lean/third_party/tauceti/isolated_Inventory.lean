import TauCeti.Analysis.Matrix.SchurComplement
import Lean

open Lean

run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`TauCeti).isPrefixOf name then
      logInfo m!"TC_MODULE {name}"
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => (`TauCeti).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if own then
      if info.isAxiom then
        throwError "Custom axiom in source closure: {name}"
      logInfo m!"TC_CONSTANT {name}"
      if info.isTheorem then
        logInfo m!"TC_THEOREM {name}"
    pure ()
  pure ()

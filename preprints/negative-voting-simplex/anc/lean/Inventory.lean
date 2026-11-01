import NegativeVoting
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`NegativeVoting).isPrefixOf name then
      logInfo m!"NV_MODULE {name}"
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    if (`NegativeVoting).isPrefixOf name then
      if info.isAxiom then
        throwError "Custom axiom in project namespace: {name}"
      if info.isTheorem then
        logInfo m!"NV_THEOREM {name}"
    pure ()
  pure ()

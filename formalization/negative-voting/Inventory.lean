import NegativeVoting
import Lean

open Lean

private def firstPartyModule (name : Name) : Bool :=
  (`NegativeVoting).isPrefixOf name ||
    #[`GaussianSpectralBridge, `GaussianSecondChaos, `GaussianAffineComparison,
      `MulgundGaussianComparison, `GaussianHypercontractivityBridge,
      `GaussianSmallCap, `GaussianCapTailAndStrip, `GaussianNormalTrace].contains name

run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if firstPartyModule name then
      logInfo m!"NV_MODULE {name}"
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => firstPartyModule env.header.moduleNames[idx.toNat]!
      | none => false
    if own then
      if info.isAxiom then
        throwError "Custom axiom in project module: {name}"
      if info.isTheorem then
        logInfo m!"NV_THEOREM {name}"
    pure ()
  pure ()

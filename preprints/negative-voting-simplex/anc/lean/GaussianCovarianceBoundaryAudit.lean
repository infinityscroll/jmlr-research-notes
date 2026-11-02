import GaussianCovarianceClosedGraph
import Lean
open Lean
run_cmd do
  let env ← getEnv
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => #[`GaussianFanMassContinuity, `GaussianCovarianceBoundaryContinuity, `GaussianCovarianceClosedGraph].contains env.header.moduleNames[idx.toNat]!
      | none => false
    if own then
      if info.isAxiom then throwError "Custom axiom in covariance boundary continuity: {name}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "Disallowed axiom {a} in {name}"
      let record := Json.mkObj [
        ("constant", toJson name.toString), ("theorem", toJson info.isTheorem),
        ("axioms", toJson (axioms.toList.map Name.toString))]
      logInfo m!"GAUSSIAN_COVARIANCE_BOUNDARY_AXIOMS {record.compress}"
    pure ()
  pure ()

import GaussianCovarianceConcavity
import Lean
open Lean Meta Elab Command
run_cmd do
  let env ← getEnv
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `GaussianCovarianceConcavity
      | none => false
    if owned then
      if info.isAxiom then throwError "Unexpected authored axiom: {name}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "Nonstandard transitive axiom {a} in {name}"
      logInfo m!"GAUSSIAN_COVARIANCE_CONCAVITY_AUDIT {Json.mkObj [
        ("constant", toJson name.toString),
        ("theorem", toJson info.isTheorem),
        ("axioms", toJson (axioms.toList.map Name.toString))] |>.compress}"
    pure ()

import GaussianUniformLocalCurvature
import Lean
open Lean
run_cmd do
  let env ← getEnv
  let modules := #[`GaussianUniformLocalCurvature]
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if modules.contains moduleName then
      if info.isAxiom then throwError "Custom axiom: {name}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "Disallowed axiom {a} in {name}"
      logInfo m!"UNIFORM_LOCAL_CURVATURE_AXIOMS {(Json.mkObj [
        ("module",toJson moduleName.toString),("constant",toJson name.toString),
        ("theorem",toJson info.isTheorem),("axioms",toJson (axioms.toList.map Name.toString))]).compress}"
    pure ()
  pure ()

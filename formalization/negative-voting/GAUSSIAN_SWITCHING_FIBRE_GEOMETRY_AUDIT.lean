import GaussianSwitchingFibreGeometry
import Lean
open Lean
run_cmd do
  let env ← getEnv
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `GaussianSwitchingFibreGeometry
      | none => false
    if own then
      if info.isAxiom then throwError "Custom axiom in GaussianSwitchingFibreGeometry: {name}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "Disallowed axiom {a} in {name}"
      let record := Json.mkObj [
        ("constant", toJson name.toString), ("theorem", toJson info.isTheorem),
        ("axioms", toJson (axioms.toList.map Name.toString))]
      logInfo m!"SWITCHING_FIBRE_GEOMETRY_AXIOMS {record.compress}"
    pure ()
  pure ()

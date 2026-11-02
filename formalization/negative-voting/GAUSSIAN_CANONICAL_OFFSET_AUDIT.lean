import GaussianFanCanonicalOffset
import Lean
open Lean
run_cmd do
  let env ← getEnv
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `GaussianFanCanonicalOffset
      | none => false
    if own then
      if info.isAxiom then throwError "Custom axiom: {name}"
      let axioms ← collectAxioms name
      for a in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains a do
          throwError "Disallowed axiom {a} in {name}"
      logInfo m!"CANONICAL_OFFSET_AXIOMS {(Json.mkObj [
        ("constant",toJson name.toString),("theorem",toJson info.isTheorem),
        ("axioms",toJson (axioms.toList.map Name.toString))]).compress}"
    pure ()
  pure ()

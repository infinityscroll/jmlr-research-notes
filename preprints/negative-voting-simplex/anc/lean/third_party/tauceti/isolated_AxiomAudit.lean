import TauCeti.Analysis.Matrix.SchurComplement
import Lean

open Lean

-- Work with compiled Names directly: this includes private declarations with numeric components.
run_cmd do
  let env ← getEnv
  let _ ← env.constants.foldM (init := ()) fun _ name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => (`TauCeti).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if own then
      if info.isAxiom then
        throwError "Custom axiom in source closure: {name}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      let record := Json.mkObj [
        ("constant", toJson name.toString),
        ("axioms", toJson (axioms.toList.map Name.toString))]
      logInfo m!"TC_AXIOM_JSON {record.compress}"
    pure ()
  pure ()

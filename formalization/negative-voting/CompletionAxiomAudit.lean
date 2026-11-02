import GaussianSquareExponential
import GaussianPolynomialHermiteDegree
import GaussianPolynomialFacetTrace
import GaussianPolynomialFacetLogBound
import GaussianQuadraticBulkDifferential
import GaussianSmoothErrorMoment
import GaussianSmoothErrorNormalDerivative
import GaussianFanQuadraticSecondDerivative
import GaussianFanMassSecondDerivative
import GaussianSecondChaosHessian
import GaussianPolynomialFacetGeometricTrace
import GaussianSmoothErrorTube
import GaussianSwitchingOrderedIntegral
import Lean

open Lean

private def completionModule (name : Name) : Bool :=
  #[`GaussianSquareExponential, `GaussianPolynomialHermiteDegree,
    `GaussianPolynomialFacetTrace, `GaussianPolynomialFacetLogBound,
    `GaussianQuadraticBulkDifferential, `GaussianSmoothErrorMoment, `GaussianSmoothErrorNormalDerivative, `GaussianFanQuadraticSecondDerivative, `GaussianFanMassSecondDerivative, `GaussianSecondChaosHessian, `GaussianPolynomialFacetGeometricTrace, `GaussianSmoothErrorTube, `GaussianSwitchingOrderedIntegral].contains name

run_cmd do
  let env ← getEnv
  let count : Nat ← env.constants.foldM (init := (0 : Nat)) fun count name info => do
    let own := match env.getModuleIdxFor? name with
      | some idx => completionModule env.header.moduleNames[idx.toNat]!
      | none => false
    if !own then return count
    if info.isAxiom then throwError "Custom axiom in completion module: {name}"
    if !info.isTheorem then return count
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    let record := Json.mkObj [
      ("constant", toJson name.toString),
      ("axioms", toJson (axioms.toList.map Name.toString))]
    logInfo m!"NV_COMPLETION_AXIOM_JSON {record.compress}"
    return count + 1
  if count == 0 then throwError "No completion theorem constants were audited"
  logInfo m!"NV_COMPLETION_THEOREMS {count}"

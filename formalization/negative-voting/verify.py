#!/usr/bin/env python3
"""Build the full negative-voting formalization and enforce its exact target and axiom boundary."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MAIN_GOAL_SHA256 = 'fe8f21515f4af803af7cbd14c3741377e6a4dcd508aeaf749a2821544c6c86c6'
FINAL_THEOREM = 'NegativeVoting.full_negative_voting'


def verify(lake: str) -> dict:
    sources = sorted((ROOT / 'NegativeVoting').rglob('*.lean')) + [ROOT / 'NegativeVoting.lean', ROOT / 'GaussianSpectralBridge.lean', ROOT / 'GaussianSecondChaos.lean', ROOT / 'GaussianAffineComparison.lean', ROOT / 'MulgundGaussianComparison.lean', ROOT / 'GaussianHypercontractivityBridge.lean', ROOT / 'GaussianSmallCap.lean', ROOT / 'GaussianCapTailAndStrip.lean', ROOT / 'GaussianNormalTrace.lean', ROOT / 'GaussianNormalDerivatives.lean', ROOT / 'GaussianFanCover.lean', ROOT / 'GaussianFacetDisintegration.lean', ROOT / 'GaussianChaosDecay.lean', ROOT / 'PolyhedralSupportBoundary.lean', ROOT / 'GaussianCapCovariance.lean', ROOT / 'GaussianCapFirstMoment.lean', ROOT / 'GaussianSmoothingComposition.lean', ROOT / 'GaussianLowModeProjection.lean', ROOT / 'GaussianWeightedFacetEnergy.lean', ROOT / 'GaussianMassCentroid.lean', ROOT / 'GaussianFacetDegree.lean', ROOT / 'GaussianCapMixedMGF.lean', ROOT / 'GaussianCapSecondMoment.lean', ROOT / 'GaussianCapCovarianceGap.lean', ROOT / 'GaussianFanMassBase.lean', ROOT / 'GaussianFanMassMinimizer.lean', ROOT / 'GaussianFanMassGradient.lean', ROOT / 'GaussianFanMassExistence.lean', ROOT / 'GaussianSoftPolyhedron.lean', ROOT / 'GaussianPolyhedronEhrhard.lean', ROOT / 'GaussianEhrhardCurvature.lean', ROOT / 'GaussianEhrhardMomentBridge.lean', ROOT / 'GaussianEhrhardCoefficient.lean', ROOT / 'GaussianFanMassJacobian.lean', ROOT / 'GaussianFanMassInverse.lean', ROOT / 'GaussianFanJacobianPseudoInverse.lean', ROOT / 'GaussianFanTestedCells.lean', ROOT / 'GaussianFanScoreHessian.lean', ROOT / 'GaussianMovingSlab.lean', ROOT / 'GaussianMovingCap.lean', ROOT / 'GaussianCapTelescoping.lean', ROOT / 'GaussianFanCycleComplex.lean', ROOT / 'GaussianFanCycleGauge.lean', ROOT / 'GaussianFanMovingCells.lean', ROOT / 'GaussianFanQuadraticHessian.lean', ROOT / 'GaussianFanSecondVariation.lean', ROOT / 'GaussianFanCentroidBoundary.lean', ROOT / 'GaussianMovingFaceMoments.lean', ROOT / 'GaussianFanCycleGeometry.lean', ROOT / 'GaussianFanCycleGram.lean', ROOT / 'GaussianFanCycleStrata.lean', ROOT / 'GaussianFanCycleCoordinates.lean', ROOT / 'GaussianFanCycleNested.lean', ROOT / 'GaussianFanCycleSlice.lean', ROOT / 'GaussianCovariancePath.lean', ROOT / 'GaussianCovariancePathRegularity.lean', ROOT / 'GaussianFanGradientDerivative.lean', ROOT / 'GaussianFanEnvelope.lean', ROOT / 'GaussianFanOffsetMinimization.lean', ROOT / 'GaussianFanCanonicalOffset.lean', ROOT / 'GaussianFanJointMass.lean', ROOT / 'GaussianFanJointInverse.lean', ROOT / 'GaussianFanCovarianceEnvelope.lean', ROOT / 'GaussianFanOptimizedValue.lean', ROOT / 'GaussianFanCovarianceHessian.lean', ROOT / 'GaussianFanCovarianceLaw.lean', ROOT / 'GaussianFanCovarianceValue.lean', ROOT / 'GaussianFanValueDerivative.lean', ROOT / 'GaussianMaximum.lean', ROOT / 'GaussianTailRatio.lean', ROOT / 'GaussianMaximumTailMargins.lean', ROOT / 'GaussianDoubleExponentialIntegral.lean', ROOT / 'GaussianMaximumMeanBounds.lean', ROOT / 'GaussianMaximumSecondMoment.lean', ROOT / 'GaussianMaximumLocalization.lean', ROOT / 'GaussianFanCycleForms.lean', ROOT / 'GaussianFanCycleMoments.lean', ROOT / 'GaussianFanCycleCoefficients.lean', ROOT / 'GaussianFanCycleFactorization.lean', ROOT / 'GaussianFanCycleBalance.lean', ROOT / 'GaussianFanCycleDeficit.lean', ROOT / 'GaussianFanCycleResidual.lean', ROOT / 'GaussianFanCycleEhrhard.lean', ROOT / 'GaussianFanCycleAnalyticBridge.lean', ROOT / 'GaussianFanCycleFlux.lean', ROOT / 'GaussianFanCycleQuadratic.lean', ROOT / 'GaussianFanCycleHessian.lean', ROOT / 'GaussianAffineBasisLower.lean', ROOT / 'GaussianCovarianceRefinedCurvature.lean', ROOT / 'GaussianL1Variance.lean', ROOT / 'GaussianCovarianceMixedEstimate.lean', ROOT / 'RegularSimplexSecondMomentAlgebra.lean', ROOT / 'GaussianFiniteGraphRayleigh.lean', ROOT / 'GaussianRegularMaximumMoments.lean', ROOT / 'GaussianRegularQuadraticGeometry.lean', ROOT / 'GaussianRegularQuadraticSymmetry.lean', ROOT / 'GaussianRegularChaosCoefficients.lean', ROOT / 'GaussianCompetitiveParity.lean', ROOT / 'GaussianFractionalMassEnergy.lean', ROOT / 'GaussianCompetitiveMassWindow.lean', ROOT / 'GaussianRegularScoreLaw.lean', ROOT / 'GaussianPositiveCovarianceFactor.lean', ROOT / 'GaussianCovarianceConcavity.lean', ROOT / 'GaussianMassProfileEnvelope.lean', ROOT / 'GaussianCovarianceStrictConcavity.lean', ROOT / 'GaussianCovarianceCoercivity.lean', ROOT / 'GaussianCovarianceOptimizer.lean', ROOT / 'GaussianPolyhedralTube.lean', ROOT / 'GaussianFanCutFrontier.lean', ROOT / 'GaussianFanBoundaryTransfer.lean', ROOT / 'GaussianCheeger.lean', ROOT / 'GaussianFanCheeger.lean', ROOT / 'GaussianFiniteGraphCoarea.lean', ROOT / 'GaussianFanRetainedCuts.lean', ROOT / 'GaussianFanRetainedGap.lean', ROOT / 'GaussianSecondChaosLower.lean', ROOT / 'GaussianRegularSecondGap.lean', ROOT / 'GaussianLocalCovarianceFactor.lean', ROOT / 'GaussianFanJointOffsets.lean', ROOT / 'GaussianFanRetainedCoefficient.lean', ROOT / 'GaussianFanJointValue.lean', ROOT / 'GaussianFanOffsetCovarianceLaw.lean', ROOT / 'GaussianFanMassValueGradient.lean', ROOT / 'GaussianFanSelectedOffsets.lean', ROOT / 'GaussianCovarianceOffsets.lean', ROOT / 'GaussianCovarianceJointValue.lean', ROOT / 'GaussianCovarianceOptimizerContinuity.lean', ROOT / 'GaussianAssignmentDuality.lean', ROOT / 'GaussianCentroidEnergyAttainment.lean', ROOT / 'GaussianReferenceSecondEnergy.lean', ROOT / 'GaussianCenteredParsevalBasis.lean', ROOT / 'GaussianMovingFaceQuadraticMoments.lean', ROOT / 'GaussianTwoCellScalar.lean', ROOT / 'GaussianTwoCellMeasure.lean', ROOT / 'GaussianTwoCellSplit.lean', ROOT / 'GaussianTwoCellSeparation.lean', ROOT / 'GaussianCovarianceOffsetResponse.lean', ROOT / 'GaussianCovariancePriceDerivative.lean', ROOT / 'GaussianCovarianceOptimizerDegree.lean', ROOT / 'GaussianCovarianceMixedDerivative.lean', ROOT / 'GaussianFanMassConcavity.lean', ROOT / 'LocalConcavity.lean', ROOT / 'GaussianFanHessianContinuity.lean', ROOT / 'GaussianFanJointValueC2.lean', ROOT / 'GaussianCovarianceJointValueC2.lean', ROOT / 'GaussianOptimizerStability.lean', ROOT / 'GaussianCovarianceOptimizerLipschitz.lean', ROOT / 'GaussianValueSemiconcavity.lean', ROOT / 'GaussianCovarianceRealization.lean', ROOT / 'GaussianBalancedReference.lean', ROOT / 'GaussianBalancedCovarianceMaximum.lean', ROOT / 'GaussianCovarianceMaximumUniqueness.lean', ROOT / 'GaussianCompetitiveSharpMass.lean', ROOT / 'GaussianCompetitiveDeficit.lean', ROOT / 'GaussianRegularCovarianceDeficit.lean', ROOT / 'GaussianFanMassContinuity.lean', ROOT / 'GaussianCovarianceBoundaryContinuity.lean', ROOT / 'GaussianCovarianceClosedGraph.lean', ROOT / 'GaussianCovarianceUniformCompact.lean', ROOT / 'GaussianCovarianceUniformTransfer.lean', ROOT / 'GaussianCovarianceOptimizerEdges.lean', ROOT / 'GaussianCovarianceOptimizerConstants.lean', ROOT / 'GaussianCovarianceUniformMixed.lean', ROOT / 'GaussianCovarianceMixedNeighborhood.lean', ROOT / 'GaussianCovarianceZeroFloorBound.lean', ROOT / 'GaussianAssignmentCoordinateBridge.lean', ROOT / 'GaussianBalancedFloorAnchor.lean', ROOT / 'GaussianAssignmentEquality.lean', ROOT / 'GaussianCovarianceMassPath.lean', ROOT / 'GaussianRegularizedMassConcavity.lean', ROOT / 'GaussianMassSemiconcavity.lean', ROOT / 'GaussianUniformMassBound.lean', ROOT / 'GaussianRegularFacetSeed.lean', ROOT / 'GaussianRegularFacetMean.lean', ROOT / 'GaussianAffineCapDerivative.lean', ROOT / 'GaussianAffineOperatorDerivative.lean', ROOT / 'GaussianAffineLogMassBound.lean', ROOT / 'GaussianAffineCapNormalization.lean', ROOT / 'GaussianAffinePathDerivative.lean', ROOT / 'GaussianAffineNormControl.lean', ROOT / 'GaussianConditionalSecondMoment.lean', ROOT / 'GaussianFacetConditionalPlane.lean', ROOT / 'GaussianCapShiftLower.lean', ROOT / 'GaussianScoreRealization.lean', ROOT / 'GaussianFacetScoreWitness.lean', ROOT / 'GaussianCapUnionLower.lean', ROOT / 'GaussianLocalCurvatureAlgebra.lean', ROOT / 'GaussianAffinePositiveMass.lean', ROOT / 'GaussianAffineLogScale.lean', ROOT / 'GaussianAffineMassComparison.lean', ROOT / 'GaussianAffinePolynomialComparison.lean', ROOT / 'GaussianRegularCapProbability.lean', ROOT / 'GaussianRegularFacetLogComparison.lean', ROOT / 'GaussianRegularFacetStability.lean', ROOT / 'GaussianRegularFacetNeighborhood.lean', ROOT / 'GaussianCovarianceSegment.lean', ROOT / 'GaussianFacetNormalExtension.lean', ROOT / 'GaussianFacetFixedCylinder.lean', ROOT / 'GaussianRegularFacetCylinder.lean', ROOT / 'GaussianOperatorHSNorm.lean', ROOT / 'GaussianFacetSchurBounds.lean', ROOT / 'GaussianFacetNormalPrefactor.lean', ROOT / 'GaussianRayDeficit.lean', ROOT / 'GaussianProcrustesDistance.lean', ROOT / 'GaussianFacetMeanBound.lean', ROOT / 'GaussianBalancedOffsetControl.lean', ROOT / 'GaussianBalancedOffsetPath.lean', ROOT / 'GaussianBalancedCovariancePath.lean', ROOT / 'GaussianCovarianceSegmentGeometry.lean', ROOT / 'GaussianBalancedFacetBootstrap.lean', ROOT / 'GaussianUniformLocalCurvature.lean', ROOT / 'GaussianConditionedFacetCap.lean', ROOT / 'GaussianConditionedFacetWitness.lean', ROOT / 'GaussianFanOffsetRange.lean', ROOT / 'GaussianConditionedFacetLower.lean', ROOT / 'GaussianRegularMassSymmetry.lean', ROOT / 'GaussianRegularOUPotential.lean', ROOT / 'GaussianRegularScoreProjection.lean', ROOT / 'GaussianRegularNoisePair.lean', ROOT / 'GaussianBalancedOffsetEstimate.lean', ROOT / 'GaussianExteriorReferenceBounds.lean', ROOT / 'GaussianExteriorOrbitBounds.lean', ROOT / 'GaussianGlobalCovarianceDeficit.lean', ROOT / 'GaussianRegularFacetGaussianLower.lean', ROOT / 'GaussianRegularMassSeparation.lean', ROOT / 'GaussianQuadraticMovingCap.lean', ROOT / 'GaussianFanQuadraticMoments.lean', ROOT / 'GaussianSecondChaosMassAdjoint.lean', ROOT / 'GaussianSecondChaosFacetGradient.lean', ROOT / 'GaussianPolynomialTiltDerivatives.lean', ROOT / 'GaussianCapPolynomialStein.lean', ROOT / 'GaussianCapPolarizedStein.lean', ROOT / 'GaussianQuarticMovingCap.lean', ROOT / 'GaussianQuadraticAffineTransport.lean', ROOT / 'GaussianFanCoherentChart.lean', ROOT / 'GaussianFanQuarticMoments.lean', ROOT / 'GaussianFanQuadraticTransport.lean', ROOT / 'GaussianRegularNoiseRoutingIntegral.lean', ROOT / 'GaussianRegularFacetRangeGeometry.lean', ROOT / 'GaussianRegularFacetRangeEnvelope.lean', ROOT / 'GaussianRegularPairRange.lean', ROOT / 'GaussianRegularPairCoefficient.lean', ROOT / 'GaussianRegularPairCoefficientBounds.lean', ROOT / 'GaussianRegularCoefficientMajorant.lean', ROOT / 'GaussianFiniteHermiteInverseOU.lean', ROOT / 'GaussianBoundedRowGraph.lean', ROOT / 'GaussianBoundedRowGap.lean', ROOT / 'GaussianBoundedOffsetResponse.lean', ROOT / 'GaussianBoundedMassTaylor.lean', ROOT / 'GaussianRowMassValueUpper.lean', ROOT / 'GaussianBoundedOffsetCertificate.lean', ROOT / 'GaussianBoundedOffsetLimit.lean', ROOT / 'GaussianPSDAffineApproximation.lean', ROOT / 'GaussianArbitraryRowOffsetCertificate.lean', ROOT / 'GaussianPrimalDualDeficit.lean', ROOT / 'GaussianCompetitiveCovarianceTransfer.lean', ROOT / 'GaussianSwitchingFibreGeometry.lean', ROOT / 'GaussianSwitchingFibreIntegration.lean', ROOT / 'GaussianSwitchingFarTail.lean', ROOT / 'GaussianSwitchingCellCoordinates.lean', ROOT / 'GaussianSwitchingPairBound.lean', ROOT / 'GaussianSquareExponential.lean', ROOT / 'GaussianPolynomialHermiteDegree.lean', ROOT / 'GaussianPolynomialFacetTrace.lean', ROOT / 'GaussianPolynomialFacetLogBound.lean', ROOT / 'GaussianCheegerRampAdapter.lean', ROOT / 'GaussianSmoothErrorMoment.lean', ROOT / 'GaussianSmoothErrorNormalDerivative.lean', ROOT / 'GaussianSmoothErrorTube.lean', ROOT / 'GaussianFanQuadraticSecondDerivative.lean', ROOT / 'GaussianFanMassSecondDerivative.lean', ROOT / 'GaussianSecondChaosHessian.lean', ROOT / 'GaussianPolynomialFacetGeometricTrace.lean', ROOT / 'GaussianSwitchingOrderedIntegral.lean', ROOT / 'GaussianSwitchingTinyScale.lean', ROOT / 'GaussianReciprocalDampingTube.lean', ROOT / 'GaussianCoherentLiftHessian.lean', ROOT / 'GaussianQuadraticBulkNorm.lean', ROOT / 'GaussianBoundedCoherentLift.lean', ROOT / 'GaussianDimensionUniformErrorBounds.lean', ROOT / 'GaussianSwitchingLpCap.lean', ROOT / 'GaussianQuadraticTensorBulkNorm.lean', ROOT / 'GaussianTensorHessianContraction.lean', ROOT / 'GaussianSwitchingLabelSum.lean', ROOT / 'GaussianFanMarginBounds.lean', ROOT / 'GaussianSwitchingMarginSeparation.lean', ROOT / 'GaussianSwitchingModerateScale.lean', ROOT / 'GaussianSwitchingModerateIntegral.lean', ROOT / 'GaussianTensorFacetAggregation.lean', ROOT / 'GaussianGlobalTensorTransport.lean', ROOT / 'GaussianRegularFacetCancellation.lean', ROOT / 'GaussianAdjustedTensorBulkNorm.lean', ROOT / 'GaussianBalancedSecondChaosDerivative.lean', ROOT / 'GaussianActualMomentOperator.lean', ROOT / 'GaussianMomentResponseBound.lean', ROOT / 'GaussianBalancedMomentComparison.lean', ROOT / 'GaussianBalancedFacetHessian.lean', ROOT / 'GaussianMassAdjointEnergy.lean', ROOT / 'GaussianReferenceJumpComparison.lean', ROOT / 'GaussianOUResidualMoment.lean', ROOT / 'GaussianRegularQuadraticRepresentation.lean', ROOT / 'GaussianCanonicalRegularFacetCancellation.lean', ROOT / 'GaussianRegularSpectatorRepresentation.lean', ROOT / 'GaussianQuadraticMomentIsometry.lean', ROOT / 'GaussianQuadraticMomentPadding.lean', ROOT / 'GaussianRegularOrbitRepresentation.lean', ROOT / 'GaussianNormalTraceAllExponents.lean', ROOT / 'GaussianActualFacetOUTrace.lean', ROOT / 'GaussianBoundaryTraceAggregation.lean', ROOT / 'GaussianBoundaryHighChaosTrace.lean', ROOT / 'GaussianFanOUTrace.lean', ROOT / 'GaussianRareLabelHighChaos.lean', ROOT / 'GaussianBoundedOUCellTests.lean', ROOT / 'GaussianNearRegularGraphGap.lean', ROOT / 'GaussianBalancedMomentGeometry.lean', ROOT / 'GaussianConditionedFacetGeneral.lean', ROOT / 'GaussianNearRegularBalancedGeometry.lean', ROOT / 'GaussianRegularReferenceJumpBound.lean', ROOT / 'GaussianBalancedOffsetComparison.lean', ROOT / 'GaussianBoundaryFunctionalRiesz.lean', ROOT / 'GaussianRegularReferenceNormalization.lean', ROOT / 'GaussianCorrectedTransportBound.lean', ROOT / 'GaussianHessianReferenceRemainder.lean', ROOT / 'GaussianBalancedEnergyComparison.lean', ROOT / 'GaussianRegularCoefficientBound.lean', ROOT / 'GaussianNearRegularNormalizedBounds.lean', ROOT / 'GaussianRegularTransportProducts.lean', ROOT / 'GaussianRegularTransportBound.lean', ROOT / 'GaussianBoundedHessianRemainder.lean', ROOT / 'GaussianNearRegularEnergyComparison.lean', ROOT / 'GaussianPathSmoothedComparison.lean', ROOT / 'GaussianCellOUContinuity.lean', ROOT / 'GaussianNearRegularEnergyLogBound.lean', ROOT / 'GaussianRegularHighTailCrossKernel.lean', ROOT / 'GaussianRegularHighTailCross.lean', ROOT / 'GaussianStructuredSwitchingNormal.lean', ROOT / 'GaussianStructuredSwitchingMoments.lean', ROOT / 'GaussianSignedHighTailComparison.lean', ROOT / 'GaussianRegularCrossPlaneGeometry.lean', ROOT / 'GaussianRegularCrossPlaneOU.lean', ROOT / 'GaussianLowModeIsometry.lean', ROOT / 'GaussianRegularCellReflection.lean', ROOT / 'GaussianRegularHighTailInputs.lean', ROOT / 'GaussianRegularHighTailCrossPlane.lean', ROOT / 'GaussianRegularHighTailCrossAggregation.lean', ROOT / 'GaussianStructuredSwitchingFacet.lean', ROOT / 'GaussianStructuredSwitchingFacetEnergy.lean', ROOT / 'GaussianStructuredResidualInputs.lean', ROOT / 'GaussianExteriorActualComparison.lean', ROOT / 'GaussianStructuredSwitchingTube.lean', ROOT / 'GaussianExteriorRoutingMargin.lean', ROOT / 'GaussianRegularHighTailCrossPath.lean', ROOT / 'GaussianQuadraticBulkDifferential.lean']
    sources.append(ROOT / 'GaussianNearBalancedSourceInputs.lean')
    sources.append(ROOT / 'GaussianRegularHighTailCrossSelected.lean')
    sources.append(ROOT / 'GaussianExteriorRoutingGeometry.lean')
    sources.append(ROOT / 'GaussianExteriorRelativeAlgebra.lean')
    sources.append(ROOT / 'GaussianExteriorSignedTailRelative.lean')
    sources.append(ROOT / 'GaussianCompetitiveTightMassWindow.lean')
    sources.append(ROOT / 'GaussianCompetitiveExteriorHighTail.lean')
    sources.append(ROOT / 'GaussianExteriorTailAbsorption.lean')
    sources.append(ROOT / 'GaussianMaximumMomentComparison.lean')
    sources.append(ROOT / 'GaussianEqualRowMaximumLaw.lean')
    sources.append(ROOT / 'GaussianMaximumUpperTail.lean')
    sources.append(ROOT / 'GaussianEqualRowMaximumComparison.lean')
    sources.append(ROOT / 'GaussianStructuredSwitchingCap.lean')
    sources.append(ROOT / 'GaussianStructuredSwitchingAmplitude.lean')
    sources.append(ROOT / 'GaussianSwitchingTinyPolynomialBounds.lean')
    sources.append(ROOT / 'GaussianNearBalancedHighTailComparison.lean')
    sources.append(ROOT / 'GaussianStructuredSwitchingAllAmplitudes.lean')
    sources.append(ROOT / 'GaussianNearBalancedStructuredCap.lean')
    sources.append(ROOT / 'GaussianStructuredAmplitudeBound.lean')
    sources.append(ROOT / 'GaussianNearBalancedActualCap.lean')
    sources.append(ROOT / 'GaussianEqualRowQuadraticCertificate.lean')
    sources.append(ROOT / 'GaussianEqualRowRoutingComparison.lean')
    sources.append(ROOT / 'GaussianCompleteGraphComponentInverse.lean')
    sources.append(ROOT / 'GaussianDiagonalHazardDifferentiation.lean')
    sources.append(ROOT / 'GaussianDiagonalHazardQuadraticForm.lean')
    sources.append(ROOT / 'GaussianCentroidOperatorBound.lean')
    sources.append(ROOT / 'GaussianGeometricMedianProxy.lean')
    sources.append(ROOT / 'GaussianOneRowCurvature.lean')
    sources.append(ROOT / 'GaussianOneRowCovarianceRay.lean')
    sources.append(ROOT / 'GaussianHazardPolynomialBounds.lean')
    sources.append(ROOT / 'GaussianNearBalancedEnergyComparison.lean')
    sources.append(ROOT / 'GaussianHazardIntegrability.lean')
    sources.append(ROOT / 'GaussianHazardThresholdBounds.lean')
    sources.append(ROOT / 'GaussianOwnCentroidRoutingCap.lean')
    sources.append(ROOT / 'GaussianOwnCentroidSpectralReplacement.lean')
    sources.append(ROOT / 'GaussianOneRowRayExclusion.lean')
    sources.append(ROOT / 'GaussianOneRowSymmetrization.lean')
    sources.append(ROOT / 'GaussianOneRowRadialCloseness.lean')
    sources.append(ROOT / 'GaussianEqualRowRegularCoefficient.lean')
    sources.append(ROOT / 'GaussianDiagonalWinnerIntegral.lean')
    sources.append(ROOT / 'GaussianDiagonalFacetIntegral.lean')
    sources.append(ROOT / 'GaussianDiagonalScoreRealization.lean')
    sources.append(ROOT / 'GaussianDiagonalBalancedDerivative.lean')
    sources.append(ROOT / 'GaussianDensityMomentBounds.lean')
    sources.append(ROOT / 'GaussianHazardMomentEnvelope.lean')
    sources.append(ROOT / 'GaussianHazardQuantileBounds.lean')
    sources.append(ROOT / 'GaussianHazardUniformCoefficientBounds.lean')
    sources.append(ROOT / 'GaussianDiagonalBalanceEquation.lean')
    sources.append(ROOT / 'GaussianRegularTieLaw.lean')
    sources.append(ROOT / 'GaussianRegularTieVariance.lean')
    sources.append(ROOT / 'GaussianCovarianceRadialNormalization.lean')
    sources.append(ROOT / 'GaussianCompetitiveEqualRowProxy.lean')
    sources.append(ROOT / 'GaussianHazardQuantileAsymptotics.lean')
    sources.append(ROOT / 'GaussianOwnCentroidLocalReplacement.lean')
    sources.append(ROOT / 'GaussianDiagonalOffsetComponentBound.lean')
    sources.append(ROOT / 'GaussianOwnCentroidQuantitativeReplacement.lean')
    sources.append(ROOT / 'GaussianHazardUniformUpperCoefficients.lean')
    sources.append(ROOT / 'GaussianHazardUniformMoments.lean')
    sources.append(ROOT / 'GaussianRegularDiagonalBalance.lean')
    sources.append(ROOT / 'GaussianStrongDiagonalCurvature.lean')
    sources.append(ROOT / 'GaussianEqualDiagonalProjection.lean')
    sources.append(ROOT / 'GaussianRegularHazardCoefficient.lean')
    sources.append(ROOT / 'GaussianHazardKernelDifferentiation.lean')
    sources.append(ROOT / 'GaussianHazardKernelPathDerivative.lean')
    sources.append(ROOT / 'GaussianDiagonalUniformOffsetBound.lean')
    sources.append(ROOT / 'GaussianHazardSecondDifferentiation.lean')
    sources.append(ROOT / 'GaussianRegularHazardDerivative.lean')
    sources.append(ROOT / 'GaussianHazardWeightedSecondBounds.lean')
    sources.append(ROOT / 'GaussianHazardSecondMomentIntegral.lean')
    sources.append(ROOT / 'GaussianDiagonalOffsetContinuation.lean')
    sources.append(ROOT / 'GaussianHazardRawIntegralDerivative.lean')
    sources.append(ROOT / 'GaussianNearRegularEnergyRectangle.lean')
    sources.append(ROOT / 'GaussianCovarianceFactorDistance.lean')
    sources.append(ROOT / 'GaussianCovarianceSupportingPriceBound.lean')
    sources.append(ROOT / 'GaussianDiagonalIntegratedLaplacian.lean')
    sources.append(ROOT / 'GaussianDiagonalCovarianceSupport.lean')
    sources.append(ROOT / 'GaussianDiagonalFrameRealization.lean')
    sources.append(ROOT / 'GaussianDiagonalDerivativeEnvelopes.lean')
    sources.append(ROOT / 'GaussianDiagonalSecondForcingBound.lean')
    sources.append(ROOT / 'GaussianDiagonalSupportAlgebra.lean')
    sources.append(ROOT / 'GaussianSummedTaylorRemainder.lean')
    sources.append(ROOT / 'GaussianSelectedOffsetSecondDerivative.lean')
    sources.append(ROOT / 'GaussianDiagonalVarianceSupport.lean')
    sources.append(ROOT / 'GaussianDiagonalSecondOffsetBound.lean')
    sources.append(ROOT / 'GaussianCovarianceDeficitRectangle.lean')
    sources.append(ROOT / 'GaussianCovarianceEnergyRectangle.lean')
    sources.append(ROOT / 'GaussianDiagonalHazardSecondControl.lean')
    sources.append(ROOT / 'GaussianHazardPolynomialIntegralDerivative.lean')
    sources.append(ROOT / 'GaussianDiagonalSecondBalanceEquation.lean')
    sources.append(ROOT / 'GaussianNormalizedDiagonalDeviation.lean')
    sources.append(ROOT / 'GaussianNormalizedRowPayment.lean')
    sources.append(ROOT / 'GaussianEqualRowProxyLoss.lean')
    sources.append(ROOT / 'GaussianCompetitiveSecondChaosComparison.lean')
    sources.append(ROOT / 'GaussianVariancePathSymmetry.lean')
    sources.append(ROOT / 'GaussianHazardSecondIntegralDerivative.lean')
    sources.append(ROOT / 'GaussianBalancedOffsetCertificateCancellation.lean')
    sources.append(ROOT / 'GaussianVarianceLocalBounds.lean')
    sources.append(ROOT / 'GaussianDiagonalHazardTaylor.lean')
    sources.append(ROOT / 'GaussianSecondChaosAbsorption.lean')
    sources.append(ROOT / 'GaussianActualRowPayment.lean')
    sources.append(ROOT / 'GaussianMainGoalAssembly.lean')
    sources.append(ROOT / 'GaussianBalancedEqualRowSecondChaos.lean')
    sources.append(ROOT / 'GaussianExteriorNoiseAssembly.lean')
    sources.append(ROOT / 'GaussianOrthantTraceCancellation.lean')
    sources.append(ROOT / 'GaussianMassHessianBulk.lean')
    sources.append(ROOT / 'GaussianEqualDiagonalOperatorProjection.lean')
    sources.append(ROOT / 'GaussianThresholdFan.lean')
    sources.append(ROOT / 'GaussianOrthantTraceAlgebra.lean')
    sources.append(ROOT / 'GaussianRelativeTailMomentComparison.lean')
    sources.append(ROOT / 'GaussianLocalRectangleAbsorption.lean')
    sources.append(ROOT / 'GaussianSecondEnergyCovarianceLaw.lean')
    sources.append(ROOT / 'GaussianThresholdCDFDerivative.lean')
    sources.append(ROOT / 'GaussianThresholdCDFTailComparison.lean')
    sources.append(ROOT / 'GaussianRelativeMomentAbsorption.lean')
    sources.append(ROOT / 'GaussianLocalOrbitDeficitPayment.lean')
    sources.append(ROOT / 'GaussianLocalNoiseAbsorption.lean')
    sources.append(ROOT / 'GaussianRelativeMomentLogAbsorption.lean')
    sources.append(ROOT / 'GaussianEqualRowLabelAugmentation.lean')
    sources.append(ROOT / 'GaussianEqualRowFreeMomentBridge.lean')
    sources.append(ROOT / 'GaussianNearBalancedEnergyMixedBound.lean')
    sources.append(ROOT / 'GaussianOwnCentroidPrimalGap.lean')
    sources.append(ROOT / 'GaussianNearBalancedTailLogBound.lean')
    sources.append(ROOT / 'GaussianNormalizedLocalGeometry.lean')
    sources.append(ROOT / 'GaussianEqualRowTailFreeComparison.lean')
    sources.append(ROOT / 'GaussianNearBalancedTailUniform.lean')
    sources.append(ROOT / 'GaussianNearBalancedNoiseAbsorption.lean')
    sources.append(ROOT / 'GaussianOwnCentroidCellNoise.lean')
    sources.append(ROOT / 'GaussianLocalOwnCentroidGeometry.lean')
    sources.append(ROOT / 'GaussianBalancedCovarianceSecondChaos.lean')
    sources.append(ROOT / 'GaussianLocalOwnCentroidRigidity.lean')
    sources.append(ROOT / 'GaussianLocalBalancedSecondChaos.lean')
    sources.append(ROOT / 'GaussianFullNegativeVoting.lean')
    main_goal_hash = hashlib.sha256((ROOT / 'NegativeVoting/MainGoal.lean').read_bytes()).hexdigest()
    if main_goal_hash != MAIN_GOAL_SHA256:
        raise RuntimeError('Original FullNegativeVotingStatement source changed')
    authored_count = 0
    for path in sources:
        text = path.read_text()
        # Proof source only: comments are removed before scanning escape hatches.
        clean = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        clean = re.sub(r'--[^\n]*', '', clean)
        authored_count += len(re.findall(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+[\w.]+', clean))
        forbidden = re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', clean)
        if forbidden:
            raise RuntimeError(f'Forbidden proof escape in {path.name}: {forbidden.group()}')
    build = subprocess.run([lake, 'build'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if build.returncode:
        print(build.stdout)
        raise RuntimeError('lake build failed')
    inventory = subprocess.run([lake, 'env', 'lean', 'Inventory.lean'], cwd=ROOT,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if inventory.returncode:
        print(inventory.stdout)
        raise RuntimeError('Compiled-environment inventory failed')
    theorem_names = re.findall(r'NV_THEOREM ([^\r\n]+)', inventory.stdout)
    imported_modules = set(re.findall(r'NV_MODULE (\S+)', inventory.stdout))
    expected_modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in sources}
    if not expected_modules <= imported_modules:
        raise RuntimeError(f'Unimported project sources: {sorted(expected_modules - imported_modules)}')
    audit = subprocess.run([lake, 'env', 'lean', 'AxiomAudit.lean'], cwd=ROOT,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if audit.returncode:
        print(audit.stdout)
        raise RuntimeError('Lean axiom audit failed')
    seen = set()
    for line in audit.stdout.splitlines():
        if not line.startswith('NV_AXIOM_JSON '):
            continue
        record = json.loads(line.split(' ', 1)[1])
        name = record['constant']
        axioms = set(record['axioms'])
        if name in seen:
            raise RuntimeError(f'Duplicate axiom audit: {name}')
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f'Unexpected axioms for {name}: {sorted(axioms - ALLOWED_AXIOMS)}')
        seen.add(name)
    if seen != set(theorem_names):
        raise RuntimeError(f'Audit inventory mismatch: {sorted(seen ^ set(theorem_names))}')
    if FINAL_THEOREM not in seen:
        raise RuntimeError('Full target theorem is absent from the compiled axiom audit')
    target = subprocess.run([lake, 'env', 'lean', 'completion-evidence/full-target-check.lean'],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if target.returncode:
        print(target.stdout)
        raise RuntimeError('Exact full-target type check failed')
    print(target.stdout, end='')
    print(build.stdout, end='')
    print(inventory.stdout, end='')
    print(audit.stdout, end='')
    return {'status': 'passed', 'theorem_count': len(theorem_names),
            'named_theorem_count': authored_count,
            'module_count': len(expected_modules),
            'full_target_theorem': FINAL_THEOREM,
            'original_main_goal_sha256': main_goal_hash,
            'allowed_logical_axioms': sorted(ALLOWED_AXIOMS),
            'scope': 'FullNegativeVotingStatement: one alphabet threshold, all permitted ambient dimensions, full negative voting interval, all AE measurable fractional simplex assignments, inequality and exact AE regular equality class'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake', help='Lake executable, normally supplied by elan')
    args = parser.parse_args()
    print(json.dumps(verify(args.lake), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError) as error:
        print(f'ERROR: {error}', file=sys.stderr)
        raise SystemExit(1)

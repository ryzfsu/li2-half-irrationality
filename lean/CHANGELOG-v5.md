# v5 changelog

This release is a fresh source export copied from v4. The working repository,
the v4 export, and their histories are unchanged.

## Source closure

Removed the following 68 `.lean` files because they are outside the declared
Lake target closure (`Li2Lean`, `Solution`, and `Challenge`). They remain in
the development repository and are not evidence for the shipped theorem:

- `Li2Lean/Agents/AuditTubeCircle.lean`
- `Li2Lean/Agents/AuditTubeCircleMeasure.lean`
- `Li2Lean/Agents/E_L6.lean`
- `Li2Lean/Audit.lean`
- `Li2Lean/Kit/AndreiefFiniteBridge.lean`
- `Li2Lean/Kit/IntegralSupFinite.lean`
- `Li2Lean/MainActualInputs.lean`
- `Li2Lean/P0/ActualReferenceQLogContourStrict.lean`
- `Li2Lean/P0/AlphaParamGeneral.lean`
- `Li2Lean/P0/AndreiefCutoffMeasure.lean`
- `Li2Lean/P0/AndreiefFinite.lean`
- `Li2Lean/P0/Audit.lean`
- `Li2Lean/P0/CA/Contour/CanonAll.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard000.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard001.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard002.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard003.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard004.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard005.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard006.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard007.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard008.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard009.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard010.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard011.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard012.lean`
- `Li2Lean/P0/CA/Contour/Rows/CShard013.lean`
- `Li2Lean/P0/CA/Receipt/Coefficient.lean`
- `Li2Lean/P0/CA/Receipt/CoefficientBridge.lean`
- `Li2Lean/P0/CA/Wire/Alpha.lean`
- `Li2Lean/P0/CA/Wire/AlphaTubeActualExplicit.lean`
- `Li2Lean/P0/ConfigContourChord.lean`
- `Li2Lean/P0/ConfigContourInteriorFormula.lean`
- `Li2Lean/P0/ConfigCstar.lean`
- `Li2Lean/P0/ConfigFamilyCount.lean`
- `Li2Lean/P0/ConfigFinalBoundActual.lean`
- `Li2Lean/P0/ConfigFrequencyEndpointSingularity.lean`
- `Li2Lean/P0/ConfigFrequencySingular.lean`
- `Li2Lean/P0/ConfigIntervalArithmetic.lean`
- `Li2Lean/P0/ConfigLiteralWeightBridge.lean`
- `Li2Lean/P0/ConfigLogScaled.lean`
- `Li2Lean/P0/ConfigPhiEvaluator.lean`
- `Li2Lean/P0/ConfigPinnedTotal.lean`
- `Li2Lean/P0/ConfigPinnedWetaExplicit.lean`
- `Li2Lean/P0/ConfigPsiQuadrature.lean`
- `Li2Lean/P0/ContourArcMeasure.lean`
- `Li2Lean/P0/DualL6FiniteEnergy.lean`
- `Li2Lean/P0/DualL6MeasureBridge.lean`
- `Li2Lean/P0/FrequencyCutoffMeasure.lean`
- `Li2Lean/P0/HighCellProfileS23.lean`
- `Li2Lean/P0/IntegerizationBottomAxioms.lean`
- `Li2Lean/P0/IntegerizationChainAxioms.lean`
- `Li2Lean/P0/IntegerizationRateBridge.lean`
- `Li2Lean/P0/IntegerizationScaledMoments.lean`
- `Li2Lean/P0/IntegerizationSmallPrimeRateBridge.lean`
- `Li2Lean/P0/NonvanishingExtendedLucas.lean`
- `Li2Lean/P0/NonvanishingUnitResidue.lean`
- `Li2Lean/P0/PinnedResidualRow4096.lean`
- `Li2Lean/P0/PinnedRow1EndpointBounds.lean`
- `Li2Lean/P0/PinnedRow1Source.lean`
- `Li2Lean/P0/PinnedRows0000_2047.lean`
- `Li2Lean/P0/PinnedRows000511.lean`
- `Li2Lean/P0/PinnedRows2048_4095.lean`
- `Li2Lean/P0/TubeCollarSweep.lean`
- `Li2Lean/P0/TubeFinalTransfer.lean`
- `Li2Lean/P0/TubeInteriorPhi.lean`
- `Li2Lean/P0/TubeSourceAtomless.lean`
- `Li2Lean/P0/TubeTransferCoefficient.lean`

The deletion was made only in this v5 export. It does not assert that these
files are mathematically irrelevant to future development.

## Documentation and audit changes

- Corrected the root-namespace name in the Challenge comment.
- Documented the actual proved constants `397/200`, `248/125`, and
  `199/100`, and separated pending comparator/nanoda checks from the build and
  axiom result.
- Added provenance for the axioms result and the declaration-level legacy
  interface scan.
- Recorded openai/math, OAI CocycleCertificate, Braams lean-codes, and the
  indirect EulerProducts provenance in `THIRD_PARTY_NOTICES.md`.
- Added the Lean-kernel-only comparator configuration under `verification/`.
- Corrected stale contour and S08 explanatory comments without changing
  theorem statements.

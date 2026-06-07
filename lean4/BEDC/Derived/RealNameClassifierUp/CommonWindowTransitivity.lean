import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierCommonWindowTransitivity [AskSetup] [PackageSetup]
    {sourceAB sourceBC commonWindow leftDyadic middleDyadic middleDyadic' rightDyadic
      toleranceAB toleranceBC refinementAB refinementBC sealAB sealBC transportAB transportBC
      replayAB replayBC provenanceAB provenanceBC localNameAB localNameBC composedTolerance
      composedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp sourceAB commonWindow leftDyadic middleDyadic toleranceAB refinementAB
        sealAB transportAB replayAB provenanceAB localNameAB bundle pkg →
      RealNameClassifierUp sourceBC commonWindow middleDyadic' rightDyadic toleranceBC
        refinementBC sealBC transportBC replayBC provenanceBC localNameBC bundle pkg →
        hsame middleDyadic middleDyadic' →
          Cont toleranceAB toleranceBC composedTolerance →
            Cont composedTolerance commonWindow composedSeal →
              PkgSig bundle composedSeal pkg →
                UnaryHistory commonWindow ∧ UnaryHistory leftDyadic ∧
                  UnaryHistory middleDyadic ∧ UnaryHistory middleDyadic' ∧
                    UnaryHistory rightDyadic ∧ UnaryHistory toleranceAB ∧
                      UnaryHistory toleranceBC ∧ UnaryHistory composedTolerance ∧
                        UnaryHistory composedSeal ∧ hsame middleDyadic middleDyadic' ∧
                          Cont toleranceAB toleranceBC composedTolerance ∧
                            Cont composedTolerance commonWindow composedSeal ∧
                              PkgSig bundle provenanceAB pkg ∧
                                PkgSig bundle provenanceBC pkg ∧
                                  PkgSig bundle composedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro packetAB packetBC sameMiddle toleranceRoute sealRoute composedSealPkg
  obtain ⟨_sourceABUnary, commonWindowUnary, leftDyadicUnary, middleDyadicUnary,
    toleranceABUnary, _refinementABUnary, _sealABUnary, _transportABUnary, _replayABUnary,
    _provenanceABUnary, _localNameABUnary, _sourceABStreamReplay, _leftMiddleTolerance,
    _toleranceABRefinementSeal, _transportABReplay, provenanceABPkg, _localNameABPkg⟩ :=
    packetAB
  obtain ⟨_sourceBCUnary, _commonWindowUnaryBC, middleDyadicUnary', rightDyadicUnary,
    toleranceBCUnary, _refinementBCUnary, _sealBCUnary, _transportBCUnary, _replayBCUnary,
    _provenanceBCUnary, _localNameBCUnary, _sourceBCStreamReplay, _middleRightTolerance,
    _toleranceBCRefinementSeal, _transportBCReplay, provenanceBCPkg, _localNameBCPkg⟩ :=
    packetBC
  have composedToleranceUnary : UnaryHistory composedTolerance :=
    unary_cont_closed toleranceABUnary toleranceBCUnary toleranceRoute
  have composedSealUnary : UnaryHistory composedSeal :=
    unary_cont_closed composedToleranceUnary commonWindowUnary sealRoute
  exact ⟨commonWindowUnary, leftDyadicUnary, middleDyadicUnary, middleDyadicUnary',
    rightDyadicUnary, toleranceABUnary, toleranceBCUnary, composedToleranceUnary,
    composedSealUnary, sameMiddle, toleranceRoute, sealRoute, provenanceABPkg, provenanceBCPkg,
    composedSealPkg⟩

end BEDC.Derived.RealNameClassifierUp

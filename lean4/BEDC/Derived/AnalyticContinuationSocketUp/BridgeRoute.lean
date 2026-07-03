import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_bridge_route [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      zetaRead branchRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg ->
      Cont output continuation zetaRead ->
        Cont output branch branchRead ->
          Cont branchRead transport boundary ->
            PkgSig bundle zetaRead pkg ->
              PkgSig bundle boundary pkg ->
                UnaryHistory output /\ UnaryHistory zetaRead /\ UnaryHistory branchRead /\
                  UnaryHistory boundary /\ Cont witness operation output /\
                    Cont output continuation zetaRead /\ Cont output continuation provenance /\
                      Cont output branch branchRead /\ Cont branchRead transport boundary /\
                        Cont branch transport continuation /\ PkgSig bundle provenance pkg /\
                          PkgSig bundle zetaRead pkg /\ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier outputContinuationZeta outputBranchRead branchReadTransportBoundary zetaPkg
    boundaryPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, witnessUnary, operationUnary, _outputUnary,
    branchUnary, transportUnary, continuationUnary, _provenanceUnary, _nameUnary,
    _sourceLeftOverlapWitness, witnessOperationOutput, branchTransportContinuation,
    outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have outputUnary : UnaryHistory output :=
    unary_cont_closed witnessUnary operationUnary witnessOperationOutput
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationZeta
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed outputUnary branchUnary outputBranchRead
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed branchReadUnary transportUnary branchReadTransportBoundary
  exact
    ⟨outputUnary,
      zetaUnary,
      branchReadUnary,
      boundaryUnary,
      witnessOperationOutput,
      outputContinuationZeta,
      outputContinuationProvenance,
      outputBranchRead,
      branchReadTransportBoundary,
      branchTransportContinuation,
      provenancePkg,
      zetaPkg,
      boundaryPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp

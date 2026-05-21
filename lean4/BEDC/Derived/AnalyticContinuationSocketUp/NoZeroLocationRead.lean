import BEDC.Derived.AnalyticContinuationSocketUp

namespace BEDC.Derived.AnalyticContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalyticContinuationSocketCarrier_no_zero_location_read [AskSetup] [PackageSetup]
    {source leftOverlap witness operation output branch transport continuation provenance name
      zeroRequest ledgerRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalyticContinuationSocketCarrier source leftOverlap witness operation output branch
        transport continuation provenance name bundle pkg →
      hsame zeroRequest branch →
        Cont zeroRequest transport ledgerRead →
          Cont ledgerRead name consumer →
            PkgSig bundle consumer pkg →
              UnaryHistory branch ∧ UnaryHistory zeroRequest ∧ UnaryHistory ledgerRead ∧
                UnaryHistory consumer ∧ Cont zeroRequest transport ledgerRead ∧
                  Cont ledgerRead name consumer ∧ Cont branch transport continuation ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameZeroRequest zeroRequestTransportLedger ledgerNameConsumer consumerPkg
  obtain ⟨_sourceUnary, _leftOverlapUnary, _witnessUnary, _operationUnary, _outputUnary,
    branchUnary, transportUnary, _continuationUnary, _provenanceUnary, nameUnary,
    _sourceLeftOverlapWitness, _witnessOperationOutput, branchTransportContinuation,
    _outputContinuationProvenance, _continuationNameProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have zeroRequestUnary : UnaryHistory zeroRequest :=
    unary_transport branchUnary (hsame_symm sameZeroRequest)
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed zeroRequestUnary transportUnary zeroRequestTransportLedger
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerReadUnary nameUnary ledgerNameConsumer
  exact
    ⟨branchUnary, zeroRequestUnary, ledgerReadUnary, consumerUnary,
      zeroRequestTransportLedger, ledgerNameConsumer, branchTransportContinuation, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.AnalyticContinuationSocketUp

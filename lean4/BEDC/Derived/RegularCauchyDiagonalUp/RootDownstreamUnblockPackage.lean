import BEDC.Derived.RegularCauchyDiagonalUp.DownstreamRoute
import BEDC.Derived.RegularCauchyDiagonalUp.FormalTargetBoundary

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_root_downstream_unblock_package [AskSetup]
    [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow fiberRead completionRead sealRead downstreamRead endpoint
      directCompletion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead fiberRead ->
          Cont selectedWindow regseqRead completionRead ->
            Cont regseqRead realSeal sealRead ->
              Cont completionRead sealRead downstreamRead ->
                Cont realSeal provenance endpoint ->
                  Cont windowLedger (append streamWindow regseqRead) directCompletion ->
                    PkgSig bundle fiberRead pkg ->
                      PkgSig bundle completionRead pkg ->
                        PkgSig bundle sealRead pkg ->
                          PkgSig bundle downstreamRead pkg ->
                            PkgSig bundle endpoint pkg ->
                              PkgSig bundle directCompletion pkg ->
                                hsame fiberRead completionRead ∧
                                  hsame completionRead directCompletion ∧
                                    hsame windowLedger sealRead ∧
                                      UnaryHistory downstreamRead ∧ UnaryHistory endpoint ∧
                                        UnaryHistory directCompletion ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle downstreamRead pkg ∧
                                              PkgSig bundle endpoint pkg ∧
                                                PkgSig bundle directCompletion pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier windowSelection fiberRoute completionRoute sealRoute downstreamRoute
    endpointRoute directCompletionRoute fiberPkg completionPkg sealPkg downstreamPkg
    endpointPkg directCompletionPkg
  obtain ⟨_selectedUnary, _fiberUnary, _completionUnary, _sealUnary, downstreamUnary,
    ledgerSameSeal, fiberSameCompletion, provenancePkg, downstreamPkgOut⟩ :=
    RegularCauchyDiagonalCarrier_downstream_route_factorization carrier windowSelection
      fiberRoute completionRoute sealRoute downstreamRoute fiberPkg completionPkg sealPkg
      downstreamPkg
  obtain ⟨_fiberSameCompletionFormal, completionSameDirect, _ledgerSameSealFormal,
    directCompletionUnary, _provenancePkgFormal⟩ :=
    RegularCauchyDiagonalCarrier_formal_target_boundary carrier windowSelection fiberRoute
      sealRoute completionRoute directCompletionRoute fiberPkg sealPkg completionPkg
      directCompletionPkg
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, realSealUnary,
    _windowLedgerUnary, provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, _carrierPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed realSealUnary provenanceUnary endpointRoute
  exact
    ⟨fiberSameCompletion, completionSameDirect, ledgerSameSeal, downstreamUnary,
      endpointUnary, directCompletionUnary, provenancePkg, downstreamPkgOut, endpointPkg,
      directCompletionPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp

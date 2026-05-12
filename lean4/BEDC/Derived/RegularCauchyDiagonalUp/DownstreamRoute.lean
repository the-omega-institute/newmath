import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_downstream_route_factorization [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      fiberRead completionRead sealRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead fiberRead ->
          Cont selectedWindow regseqRead completionRead ->
            Cont regseqRead realSeal sealRead ->
              Cont completionRead sealRead downstreamRead ->
                PkgSig bundle fiberRead pkg ->
                  PkgSig bundle completionRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      PkgSig bundle downstreamRead pkg ->
                        UnaryHistory selectedWindow ∧ UnaryHistory fiberRead ∧
                          UnaryHistory completionRead ∧ UnaryHistory sealRead ∧
                            UnaryHistory downstreamRead ∧ hsame windowLedger sealRead ∧
                              hsame fiberRead completionRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle downstreamRead pkg := by
  intro carrier windowSelection fiberRoute completionRoute sealRoute downstreamRoute
  intro _fiberPkg _completionPkg _sealPkg downstreamPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have fiberUnary : UnaryHistory fiberRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary fiberRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed completionUnary sealUnary downstreamRoute
  have ledgerSameSeal : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealRoute
  have fiberSameCompletion : hsame fiberRead completionRead :=
    cont_deterministic fiberRoute completionRoute
  exact
    ⟨selectedWindowUnary, fiberUnary, completionUnary, sealUnary, downstreamUnary,
      ledgerSameSeal, fiberSameCompletion, provenancePkg, downstreamPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp

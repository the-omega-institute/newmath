import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_limit_seal_route_stability [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' _endpoint' sealRead sealRead' comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame window window' ->
        hsame modulus modulus' ->
          hsame tolerance tolerance' ->
            hsame ledger ledger' ->
              hsame regseq regseq' ->
                hsame realSeal realSeal' ->
                  hsame transport transport' ->
                    hsame route route' ->
                      hsame provenance provenance' ->
                        hsame localCert localCert' ->
                          Cont route realSeal sealRead ->
                            Cont route' realSeal' sealRead' ->
                              Cont sealRead sealRead' comparison ->
                                PkgSig bundle comparison pkg ->
                                  hsame sealRead sealRead' ∧ UnaryHistory comparison ∧
                                    Cont route realSeal sealRead ∧
                                      Cont route' realSeal' sealRead' ∧
                                        Cont sealRead sealRead' comparison ∧
                                          PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier _sameWindow _sameModulus _sameTolerance _sameLedger _sameRegseq sameRealSeal
    _sameTransport sameRoute _sameProvenance _sameLocalCert routeRealSealRead
    routeRealSealRead' sealComparison comparisonPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed routeUnary realSealUnary routeRealSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed routeUnary' realSealUnary' routeRealSealRead'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameRoute sameRealSeal routeRealSealRead routeRealSealRead'
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed sealReadUnary sealReadUnary' sealComparison
  exact
    ⟨sameSealRead, comparisonUnary, routeRealSealRead, routeRealSealRead',
      sealComparison, comparisonPkg⟩

end BEDC.Derived.CauchyCriterionUp

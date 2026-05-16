import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_streamname_four_face_pullback_correspondence
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      streamRead dyadicRead tailRead sealRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont window tolerance streamRead ->
        Cont modulus tolerance dyadicRead ->
          Cont ledger regseq tailRead ->
            Cont regseq realSeal sealRead ->
              Cont streamRead sealRead pullback ->
                PkgSig bundle pullback pkg ->
                  UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory pullback ∧ Cont window tolerance streamRead ∧
                        Cont modulus tolerance dyadicRead ∧ Cont ledger regseq tailRead ∧
                          Cont regseq realSeal sealRead ∧
                            Cont streamRead sealRead pullback ∧
                              PkgSig bundle endpoint pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier streamRoute dyadicRoute tailRoute sealRoute pullbackRoute pullbackPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary toleranceUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed modulusUnary toleranceUnary dyadicRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed ledgerUnary regseqUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary realSealUnary sealRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed streamUnary sealUnary pullbackRoute
  exact
    ⟨streamUnary, dyadicUnary, tailUnary, sealUnary, pullbackUnary, streamRoute,
      dyadicRoute, tailRoute, sealRoute, pullbackRoute, endpointPkg, pullbackPkg⟩

end BEDC.Derived.CauchyCriterionUp

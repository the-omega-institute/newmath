import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_cauchy_limitseal_readback [AskSetup]
    [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      windowRead dyadicRead regseqRead sealRead limitSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg ->
      Cont precision window windowRead ->
        Cont window dyadic dyadicRead ->
          Cont dyadic regseq regseqRead ->
            Cont regseq sealRow sealRead ->
              Cont sealRead endpoint limitSealRead ->
                PkgSig bundle limitSealRead pkg ->
                  UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                    UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory limitSealRead ∧
                          Cont precision window windowRead ∧ Cont window dyadic dyadicRead ∧
                            Cont dyadic regseq regseqRead ∧ Cont regseq sealRow sealRead ∧
                              Cont sealRead endpoint limitSealRead ∧
                                PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle limitSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier precisionWindowRead windowDyadicRead dyadicRegseqRead regseqSealRead
    sealEndpointLimitRead limitPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed precisionUnary windowUnary precisionWindowRead
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary regseqUnary dyadicRegseqRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealUnary regseqSealRead
  have limitSealReadUnary : UnaryHistory limitSealRead :=
    unary_cont_closed sealReadUnary endpointUnary sealEndpointLimitRead
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, windowReadUnary,
      dyadicReadUnary, regseqReadUnary, sealReadUnary, limitSealReadUnary,
      precisionWindowRead, windowDyadicRead, dyadicRegseqRead, regseqSealRead,
      sealEndpointLimitRead, endpointPkg, limitPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp

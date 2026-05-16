import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_real_completion_diagonal_route [AskSetup]
    [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      windowRead dyadicRead regseqRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg ->
      Cont precision window windowRead ->
        Cont window dyadic dyadicRead ->
          Cont dyadic regseq regseqRead ->
            Cont regseq sealRow sealRead ->
              Cont sealRead endpoint completionRead ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                    UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                          Cont precision window windowRead ∧ Cont window dyadic dyadicRead ∧
                            Cont dyadic regseq regseqRead ∧ Cont regseq sealRow sealRead ∧
                              Cont sealRead endpoint completionRead ∧ PkgSig bundle endpoint pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier precisionWindowRead windowDyadicRead dyadicRegseqRead regseqSealRead
    sealEndpointCompletion completionPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute,
    _routeProvenanceEndpoint, _endpointLocalCert, endpointPkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed precisionUnary windowUnary precisionWindowRead
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary regseqUnary dyadicRegseqRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealUnary regseqSealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary endpointUnary sealEndpointCompletion
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, windowReadUnary,
      dyadicReadUnary, regseqReadUnary, sealReadUnary, completionReadUnary,
      precisionWindowRead, windowDyadicRead, dyadicRegseqRead, regseqSealRead,
      sealEndpointCompletion, endpointPkg, completionPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp

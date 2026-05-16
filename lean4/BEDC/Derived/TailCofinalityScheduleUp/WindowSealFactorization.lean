import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_window_seal_factorization [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      thresholdRead readbackRead sealFactor : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont window dyadic thresholdRead →
        Cont thresholdRead regseq readbackRead →
          Cont readbackRead sealRow sealFactor →
            PkgSig bundle sealFactor pkg →
              UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                UnaryHistory regseq ∧ UnaryHistory sealRow ∧
                  UnaryHistory thresholdRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealFactor ∧ Cont precision window dyadic ∧
                      Cont window dyadic thresholdRead ∧
                        Cont thresholdRead regseq readbackRead ∧
                          Cont readbackRead sealRow sealFactor ∧
                            PkgSig bundle endpoint pkg ∧
                              PkgSig bundle sealFactor pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowDyadicThreshold thresholdRegseqReadback readbackSealFactor
    sealFactorPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicThreshold
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed thresholdUnary regseqUnary thresholdRegseqReadback
  have sealFactorUnary : UnaryHistory sealFactor :=
    unary_cont_closed readbackUnary sealUnary readbackSealFactor
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, thresholdUnary,
      readbackUnary, sealFactorUnary, precisionWindowDyadic, windowDyadicThreshold,
      thresholdRegseqReadback, readbackSealFactor, endpointPkg, sealFactorPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp

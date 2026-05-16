import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_streamname_regseqrat_real_window_determinacy
    [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      realWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont regseq sealRow realWindow →
        PkgSig bundle realWindow pkg →
          UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory realWindow ∧
              Cont precision window dyadic ∧ Cont dyadic regseq sealRow ∧
                Cont regseq sealRow realWindow ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle realWindow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle
  intro carrier regseqSealRealWindow realWindowPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed regseqUnary sealUnary regseqSealRealWindow
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, realWindowUnary,
      precisionWindowDyadic, dyadicRegseqSeal, regseqSealRealWindow, endpointPkg,
      realWindowPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp

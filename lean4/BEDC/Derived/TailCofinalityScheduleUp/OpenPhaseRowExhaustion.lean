import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_open_phase_row_exhaustion [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      openPhase : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont endpoint localCert openPhase →
        PkgSig bundle openPhase pkg →
          UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory endpoint ∧ UnaryHistory openPhase ∧
                  Cont precision window dyadic ∧ Cont dyadic regseq sealRow ∧
                    Cont sealRow transport route ∧ Cont route provenance endpoint ∧
                      Cont endpoint localCert openPhase ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle openPhase pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier endpointLocalCertOpen openPhasePkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    transportUnary, routeUnary, provenanceUnary, localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, sealTransportRoute, routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have openPhaseUnary : UnaryHistory openPhase :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertOpen
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, transportUnary,
      routeUnary, provenanceUnary, localCertUnary, endpointUnary, openPhaseUnary,
      precisionWindowDyadic, dyadicRegseqSeal, sealTransportRoute, routeProvenanceEndpoint,
      endpointLocalCertOpen, endpointPkg, openPhasePkg⟩

end BEDC.Derived.TailCofinalityScheduleUp

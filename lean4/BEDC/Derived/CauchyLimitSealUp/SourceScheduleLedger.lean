import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_source_schedule_ledger_coherence [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal completionRead ->
            hsame dyadic observation ->
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
                UnaryHistory observation ∧ Cont source schedule dyadic ∧
                  Cont schedule source window ∧ Cont window dyadic observation ∧
                    hsame sealRow completionRead ∧
                      hsame endpoint (append provenance localCert) ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    sameDyadicObservation
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have sameSealCompletion : hsame sealRow completionRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨sourceUnary, scheduleUnary, windowUnary, observationUnary, sourceScheduleDyadic,
      scheduleSourceWindow, windowDyadicObservation, sameSealCompletion, sameEndpoint,
      endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

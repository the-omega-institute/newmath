import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_completion_consumer_replay [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint window
      observation replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg →
      Cont schedule source window →
        Cont window dyadic observation →
          Cont observation diagonal replay →
            hsame dyadic observation →
              UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory replay ∧
                Cont schedule source window ∧ Cont window dyadic observation ∧
                  Cont observation diagonal replay ∧ hsame sealRow replay ∧
                    hsame endpoint (append provenance localCert) ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalReplay
    sameDyadicObservation
  rcases carrier with
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
      _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
      _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
      _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalReplay
  have sameSealReplay : hsame sealRow replay :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalReplay
  exact
    ⟨windowUnary, observationUnary, replayUnary, scheduleSourceWindow,
      windowDyadicObservation, observationDiagonalReplay, sameSealReplay, sameEndpoint,
      endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

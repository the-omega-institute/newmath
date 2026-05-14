import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_source_schedule_lattice_coherence [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint window
      observation realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont source schedule window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            hsame dyadic observation ->
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory dyadic ∧
                UnaryHistory diagonal ∧ UnaryHistory window ∧ UnaryHistory observation ∧
                  UnaryHistory realRead ∧ hsame sealRow realRead ∧
                    hsame endpoint (append provenance localCert) ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleWindow windowDyadicObservation observationDiagonalRead
    sameDyadicObservation
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have sameSealRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, windowUnary, observationUnary,
      realReadUnary, sameSealRead, sameEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

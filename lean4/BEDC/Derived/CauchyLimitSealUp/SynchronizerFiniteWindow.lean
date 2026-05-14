import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_synchronizer_finite_window_nonescape
    [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead synchronizerRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg →
      Cont schedule source window →
      Cont window dyadic observation →
      Cont observation diagonal realRead →
      Cont realRead endpoint synchronizerRead →
      Cont synchronizerRead transportRow finalRead →
      hsame dyadic observation →
      PkgSig bundle finalRead pkg →
        UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
          UnaryHistory synchronizerRead ∧ UnaryHistory finalRead ∧ hsame sealRow realRead ∧
            hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointSynchronizer synchronizerTransportFinal sameDyadicObservation finalPkg
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed realReadUnary endpointUnary readEndpointSynchronizer
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed synchronizerUnary transportUnary synchronizerTransportFinal
  have sameSealRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, synchronizerUnary, finalUnary,
      sameSealRead, sameEndpoint, endpointPkg, finalPkg⟩

end BEDC.Derived.CauchyLimitSealUp

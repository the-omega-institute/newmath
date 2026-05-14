import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_streamname_dependency [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead consumerRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg →
      Cont schedule source window →
        Cont window dyadic observation →
          Cont observation diagonal realRead →
            Cont realRead endpoint consumerRead →
              Cont window source regularRead →
                hsame dyadic observation →
                  UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                    UnaryHistory consumerRead ∧ UnaryHistory regularRead ∧
                      Cont schedule source window ∧ Cont window dyadic observation ∧
                        Cont observation diagonal realRead ∧
                          Cont realRead endpoint consumerRead ∧
                            Cont window source regularRead ∧ hsame sealRow realRead ∧
                              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointConsumer windowSourceRegular sameDyadicObservation
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicObservation
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed observationUnary diagonalUnary observationDiagonalRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed realReadUnary endpointUnary readEndpointConsumer
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary sourceUnary windowSourceRegular
  have sealSameRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicObservation (hsame_refl diagonal) dyadicDiagonalSeal
      observationDiagonalRead
  exact
    ⟨windowUnary, observationUnary, realReadUnary, consumerReadUnary, regularReadUnary,
      scheduleSourceWindow, windowDyadicObservation, observationDiagonalRead,
      readEndpointConsumer, windowSourceRegular, sealSameRead, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

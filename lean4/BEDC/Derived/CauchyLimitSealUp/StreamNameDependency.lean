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

theorem CauchyLimitSealCarrier_streamname_real_terminal_handoff [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transport provenance localCert endpoint
      scheduledWindow regularRead realRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transport provenance
        localCert endpoint bundle pkg ->
      Cont schedule source scheduledWindow ->
        Cont scheduledWindow dyadic regularRead ->
          Cont regularRead diagonal realRead ->
            Cont realRead sealRow terminalRead ->
              hsame dyadic regularRead ->
                UnaryHistory scheduledWindow ∧ UnaryHistory regularRead ∧
                  UnaryHistory realRead ∧ UnaryHistory terminalRead ∧ hsame sealRow realRead ∧
                    Cont schedule source scheduledWindow ∧
                      Cont scheduledWindow dyadic regularRead ∧
                        Cont regularRead diagonal realRead ∧
                          Cont realRead sealRow terminalRead ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicRegular regularDiagonalRead
    readSealTerminal sameDyadicRegular
  obtain ⟨sourceUnary, scheduleUnary, dyadicUnary, diagonalUnary, sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpoint, endpointPkg⟩ := carrier
  have scheduledWindowUnary : UnaryHistory scheduledWindow :=
    unary_cont_closed scheduleUnary sourceUnary scheduleSourceWindow
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduledWindowUnary dyadicUnary windowDyadicRegular
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularReadUnary diagonalUnary regularDiagonalRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed realReadUnary sealUnary readSealTerminal
  have sealSameRead : hsame sealRow realRead :=
    cont_respects_hsame sameDyadicRegular (hsame_refl diagonal) dyadicDiagonalSeal
      regularDiagonalRead
  exact
    ⟨scheduledWindowUnary, regularReadUnary, realReadUnary, terminalReadUnary,
      sealSameRead, scheduleSourceWindow, windowDyadicRegular, regularDiagonalRead,
      readSealTerminal, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

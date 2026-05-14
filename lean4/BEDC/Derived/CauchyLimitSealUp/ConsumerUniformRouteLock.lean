import BEDC.Derived.CauchyLimitSealUp

namespace BEDC.Derived.CauchyLimitSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyLimitSealCarrier_consumer_uniform_route_lock [AskSetup] [PackageSetup]
    {source schedule dyadic diagonal sealRow transportRow provenance localCert endpoint window
      observation realRead consumerRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitSealCarrier source schedule dyadic diagonal sealRow transportRow provenance
        localCert endpoint bundle pkg ->
      Cont schedule source window ->
        Cont window dyadic observation ->
          Cont observation diagonal realRead ->
            Cont realRead endpoint consumerRead ->
              Cont source schedule uniformRead ->
                hsame dyadic observation ->
                  UnaryHistory window ∧ UnaryHistory observation ∧ UnaryHistory realRead ∧
                    UnaryHistory consumerRead ∧ UnaryHistory uniformRead ∧
                      hsame sealRow realRead ∧ hsame endpoint (append provenance localCert) ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier scheduleSourceWindow windowDyadicObservation observationDiagonalRead
    readEndpointConsumer sourceScheduleUniform sameDyadicObservation
  have scheduled :=
    CauchyLimitSealCarrier_scheduled_window_pullback carrier scheduleSourceWindow
      windowDyadicObservation observationDiagonalRead readEndpointConsumer sameDyadicObservation
  obtain ⟨windowUnary, observationUnary, realReadUnary, consumerReadUnary, sameSealRead,
    sameEndpoint, endpointPkg⟩ := scheduled
  obtain ⟨sourceUnary, scheduleUnary, _dyadicUnary, _diagonalUnary, _sealUnary,
    _transportUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _sourceScheduleDyadic, _dyadicDiagonalSeal, _sealTransportProvenance,
    _provenanceLocalEndpoint, _sameEndpointCarrier, _endpointPkgCarrier⟩ := carrier
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleUniform
  exact
    ⟨windowUnary, observationUnary, realReadUnary, consumerReadUnary, uniformReadUnary,
      sameSealRead, sameEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyLimitSealUp

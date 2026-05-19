import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_normal_form_consumer_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead transports downstream ->
          Cont downstream routes consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory terminal ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
                UnaryHistory normalRead ∧ UnaryHistory downstream ∧ UnaryHistory routes ∧
                  UnaryHistory consumer ∧ Cont terminal normal continuation ∧
                    Cont normal continuation normalRead ∧
                      Cont normalRead transports downstream ∧
                        Cont downstream routes consumer ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesConsumer
    consumerPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  exact
    ⟨terminalUnary, normalUnary, continuationUnary, normalReadUnary, downstreamUnary,
      routesUnary, consumerUnary, terminalNormalContinuation, normalContinuationRead,
      normalReadTransportsDownstream, downstreamRoutesConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp

import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootObligationDownstreamHandoff [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead transports downstream ->
          PkgSig bundle downstream pkg ->
            UnaryHistory typed ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
              UnaryHistory normalRead ∧ UnaryHistory transports ∧ UnaryHistory downstream ∧
                Cont typed fuel terminal ∧ Cont normal continuation normalRead ∧
                  Cont normalRead transports downstream ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamPkg
  obtain ⟨typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  exact
    ⟨typedUnary, normalUnary, continuationUnary, normalReadUnary, transportsUnary,
      downstreamUnary, typedFuelTerminal, normalContinuationRead, normalReadTransportsDownstream,
      provenancePkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp

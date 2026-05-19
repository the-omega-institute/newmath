import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_normal_word_route_exposure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        PkgSig bundle normalRead pkg ->
          UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
            Cont normal continuation normalRead ∧ Cont typed fuel terminal ∧
              Cont terminal normal continuation ∧ PkgSig bundle normalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  exact
    ⟨normalUnary, continuationUnary, normalReadUnary, normalContinuationRead,
      typedFuelTerminal, terminalNormalContinuation, normalReadPkg⟩

end BEDC.Derived.ZnormalUp

import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootSiblingNormalWordConsumption [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        PkgSig bundle normalRead pkg →
          UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
            Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
              Cont continuation transports routes ∧ Cont normal continuation normalRead ∧
                PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle normalRead pkg ∧
                    (Cont normalRead (BHist.e0 hostTail) normal → False) ∧
                      (Cont normalRead (BHist.e1 hostTail) normal → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have e0Refusal : Cont normalRead (BHist.e0 hostTail) normal → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left normalContinuationRead back
  have e1Refusal : Cont normalRead (BHist.e1 hostTail) normal → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right normalContinuationRead back
  exact
    ⟨normalUnary, continuationUnary, normalReadUnary, typedFuelTerminal,
      terminalNormalContinuation, continuationTransportsRoutes, normalContinuationRead, namePkg,
      provenancePkg, normalReadPkg, e0Refusal, e1Refusal⟩

theorem ZnormalPacket_root_normalword_route_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      normalwordRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead routes normalwordRoute →
          PkgSig bundle normalwordRoute pkg →
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
              UnaryHistory routes ∧ UnaryHistory normalwordRoute ∧
                Cont normal continuation normalRead ∧
                  Cont normalRead routes normalwordRoute ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle provenance pkg ∧
                      PkgSig bundle normalwordRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadRoutesNormalword normalwordRoutePkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have normalwordRouteUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesNormalword
  exact
    ⟨normalUnary, continuationUnary, normalReadUnary, routesUnary, normalwordRouteUnary,
      normalContinuationRead, normalReadRoutesNormalword, namePkg, provenancePkg,
      normalwordRoutePkg⟩

end BEDC.Derived.ZnormalUp

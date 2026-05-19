import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_classifier_stability [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont terminal normal terminalRead ->
          PkgSig bundle normalRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory terminal ∧
                UnaryHistory normalRead ∧ UnaryHistory terminalRead ∧
                  Cont normal continuation normalRead ∧ Cont terminal normal terminalRead ∧
                    Cont continuation transports routes ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle normalRead pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead terminalNormalRead normalReadPkg terminalReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRead
  exact
    ⟨normalUnary, continuationUnary, terminalUnary, normalReadUnary, terminalReadUnary,
      normalContinuationRead, terminalNormalRead, continuationTransportsRoutes, provenancePkg,
      normalReadPkg, terminalReadPkg⟩

end BEDC.Derived.ZnormalUp

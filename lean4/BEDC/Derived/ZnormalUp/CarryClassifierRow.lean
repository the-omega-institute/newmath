import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalCarryClassifierRow [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports handoff →
          PkgSig bundle handoff pkg →
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
              UnaryHistory handoff ∧ Cont terminal normal continuation ∧
                Cont normal continuation normalRead ∧ Cont normalRead transports handoff ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead normalReadTransportsHandoff handoffPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsHandoff
  exact
    ⟨normalUnary, continuationUnary, normalReadUnary, handoffUnary,
      terminalNormalContinuation, normalContinuationRead, normalReadTransportsHandoff,
      provenancePkg, handoffPkg⟩

end BEDC.Derived.ZnormalUp

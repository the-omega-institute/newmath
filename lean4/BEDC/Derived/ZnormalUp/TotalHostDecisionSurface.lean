import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTotalHostDecisionSurface [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      decisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont continuation routes decisionRead →
        PkgSig bundle decisionRead pkg →
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory routes ∧
              UnaryHistory decisionRead ∧ Cont typed fuel terminal ∧
                Cont terminal normal continuation ∧ Cont continuation routes decisionRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle decisionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet continuationRoutesDecision decisionPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, _provenancePkg⟩ :=
    packet
  have decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed continuationUnary routesUnary continuationRoutesDecision
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary, routesUnary,
      decisionReadUnary, typedFuelTerminal, terminalNormalContinuation,
      continuationRoutesDecision, namePkg, decisionPkg⟩

end BEDC.Derived.ZnormalUp

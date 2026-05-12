import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolePlacementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PolePlacementCarrier [AskSetup] [PackageSetup]
    (state input transition inputMatrix gain closedLoop target comparison transport routes
      provenance boundary : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory target ∧
      UnaryHistory provenance ∧ UnaryHistory boundary ∧ Cont transition gain closedLoop ∧
        Cont closedLoop target comparison ∧ Cont comparison transport routes ∧
          PkgSig bundle provenance pkg

theorem PolePlacementCarrier_closed_loop_ledger [AskSetup] [PackageSetup]
    {state input transition inputMatrix gain closedLoop target comparison transport routes
      provenance boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolePlacementCarrier state input transition inputMatrix gain closedLoop target comparison
        transport routes provenance boundary bundle pkg ->
      UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
        UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory closedLoop ∧
          UnaryHistory target ∧ UnaryHistory comparison ∧ UnaryHistory provenance ∧
            Cont transition gain closedLoop ∧ Cont closedLoop target comparison ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, targetUnary,
    provenanceUnary, _boundaryUnary, closedLoopRoute, comparisonRoute, _routesRoute,
    provenancePkg⟩ := carrier
  have closedLoopUnary : UnaryHistory closedLoop :=
    unary_cont_closed transitionUnary gainUnary closedLoopRoute
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed closedLoopUnary targetUnary comparisonRoute
  exact
    ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, closedLoopUnary,
      targetUnary, comparisonUnary, provenanceUnary, closedLoopRoute, comparisonRoute,
      provenancePkg⟩

end BEDC.Derived.PolePlacementUp

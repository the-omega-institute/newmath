import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMidpointCarrier [AskSetup] [PackageSetup]
    (left right scale midpoint branch window sameRows route provenance nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scale ∧ UnaryHistory midpoint ∧
    UnaryHistory branch ∧ UnaryHistory window ∧ UnaryHistory sameRows ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ UnaryHistory endpoint ∧
        hsame midpoint (append scale (append left right)) ∧ Cont sameRows route endpoint ∧
          PkgSig bundle endpoint pkg

theorem DyadicMidpointBranchRow_consumer_handoff [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows route provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows route provenance nameCert
        endpoint bundle pkg ->
      exists handoff : BHist,
        UnaryHistory handoff ∧ hsame handoff (append branch window) ∧
          hsame midpoint (append scale (append left right)) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, _scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _endpointUnary, midpointRow,
    _endpointRoute, pkgEndpoint⟩ := carrier
  let handoff : BHist := append branch window
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed branchUnary windowUnary (rfl : Cont branch window handoff)
  exact ⟨handoff, handoffUnary, rfl, midpointRow, pkgEndpoint⟩

end BEDC.Derived.DyadicMidpointUp

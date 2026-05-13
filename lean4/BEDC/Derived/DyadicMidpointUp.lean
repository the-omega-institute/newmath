import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMidpointCarrier [AskSetup] [PackageSetup]
    (left right scale midpoint branch window sameRows transport route provenance nameCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scale ∧ UnaryHistory midpoint ∧
    UnaryHistory branch ∧ UnaryHistory window ∧ UnaryHistory sameRows ∧ UnaryHistory route ∧
      UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        UnaryHistory endpoint ∧ hsame midpoint (append scale (append left right)) ∧
          Cont sameRows route endpoint ∧ Cont left right scale ∧ Cont scale midpoint window ∧
            Cont branch window route ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem DyadicMidpointBranchRow_consumer_handoff [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      exists handoff : BHist,
        UnaryHistory handoff ∧ hsame handoff (append branch window) ∧
          hsame midpoint (append scale (append left right)) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, _scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, midpointRow, _endpointRoute, _scaleRoute, _midpointRoute, _branchRoute,
    pkgEndpoint, _provenancePkg, _nameCertPkg⟩ := carrier
  let handoff : BHist := append branch window
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed branchUnary windowUnary (rfl : Cont branch window handoff)
  exact ⟨handoff, handoffUnary, rfl, midpointRow, pkgEndpoint⟩

theorem DyadicMidpointCarrier_readback_closure [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      UnaryHistory window ∧ UnaryHistory route ∧ Cont scale midpoint window ∧
        Cont branch window route ∧ PkgSig bundle nameCert pkg := by
  intro carrier
  obtain ⟨_leftUnary, _rightUnary, scaleUnary, midpointUnary, branchUnary,
    _windowUnary, _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary,
    _nameCertUnary, _endpointUnary, _midpointRow, _endpointRoute, _scaleRoute, midpointRoute,
    branchRoute, _endpointPkg, _provenancePkg, nameCertPkg⟩ := carrier
  have windowClosed : UnaryHistory window :=
    unary_cont_closed scaleUnary midpointUnary midpointRoute
  have routeClosed : UnaryHistory route :=
    unary_cont_closed branchUnary windowClosed branchRoute
  exact ⟨windowClosed, routeClosed, midpointRoute, branchRoute, nameCertPkg⟩

theorem DyadicMidpointCarrier_endpoint_classifier_stability [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert
      endpoint endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont left right endpointRead ->
        hsame endpointRead scale ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scale ∧
            UnaryHistory endpointRead ∧ Cont left right scale ∧
              Cont left right endpointRead ∧ hsame endpointRead scale ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier endpointReadRoute endpointReadSame
  obtain ⟨leftUnary, rightUnary, scaleUnary, _midpointUnary, _branchUnary, _windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointRow, _endpointRoute, scaleRoute, _midpointRoute, _branchRoute,
    endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointReadRoute
  exact
    ⟨leftUnary, rightUnary, scaleUnary, endpointReadUnary, scaleRoute, endpointReadRoute,
      endpointReadSame, endpointPkg⟩

end BEDC.Derived.DyadicMidpointUp

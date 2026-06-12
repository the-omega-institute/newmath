import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicMidpointEndpointSourceRoute [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      endpointRead midpointRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont left right endpointRead ->
        Cont endpointRead scale midpointRead ->
          Cont midpointRead branch branchRead ->
            PkgSig bundle branchRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row left ∨ hsame row right ∨ hsame row scale ∨
                        hsame row midpoint ∨ hsame row branch ∨ hsame row window ∨
                          hsame row branchRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont left right endpointRead ∧
                        Cont endpointRead scale midpointRead ∧
                          Cont midpointRead branch branchRead ∧ PkgSig bundle branchRead pkg)
                    hsame ∧
                UnaryHistory endpointRead ∧ UnaryHistory midpointRead ∧
                  UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier endpointRoute midpointRoute branchRoute branchPkg
  obtain ⟨leftUnary, rightUnary, scaleUnary, _midpointUnary, branchUnary, _windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointRow, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, _endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have midpointReadUnary : UnaryHistory midpointRead :=
    unary_cont_closed endpointReadUnary scaleUnary midpointRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed midpointReadUnary branchUnary branchRoute
  have sourceBranch :
      (fun row : BHist => hsame row branchRead ∧ UnaryHistory row) branchRead := by
    exact ⟨hsame_refl branchRead, branchReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
              hsame row branch ∨ hsame row window ∨ hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right endpointRead ∧
              Cont endpointRead scale midpointRead ∧ Cont midpointRead branch branchRead ∧
                PkgSig bundle branchRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead sourceBranch
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, midpointRoute, branchRoute, branchPkg⟩
  }
  exact ⟨cert, endpointReadUnary, midpointReadUnary, branchReadUnary⟩

theorem DyadicMidpointBranchComparisonHandoff [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      endpointRead midpointRead branchRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont left right endpointRead ->
        Cont endpointRead scale midpointRead ->
          Cont midpointRead branch branchRead ->
            Cont branchRead window handoffRead ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row left ∨ hsame row right ∨ hsame row scale ∨
                          hsame row midpoint ∨ hsame row branch ∨ hsame row window ∨
                            hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont left right endpointRead ∧
                          Cont endpointRead scale midpointRead ∧
                            Cont midpointRead branch branchRead ∧
                              Cont branchRead window handoffRead ∧
                                PkgSig bundle handoffRead pkg)
                      hsame ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier endpointRoute midpointRoute branchRoute handoffRoute handoffPkg
  obtain ⟨leftUnary, rightUnary, scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointRow, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, _endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have midpointReadUnary : UnaryHistory midpointRead :=
    unary_cont_closed endpointReadUnary scaleUnary midpointRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed midpointReadUnary branchUnary branchRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed branchReadUnary windowUnary handoffRoute
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
              hsame row branch ∨ hsame row window ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right endpointRead ∧
              Cont endpointRead scale midpointRead ∧ Cont midpointRead branch branchRead ∧
                Cont branchRead window handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, midpointRoute, branchRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, handoffReadUnary⟩

end BEDC.Derived.DyadicMidpointUp

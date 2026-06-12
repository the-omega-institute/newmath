import BEDC.Derived.DyadicMidpointUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMidpointRadiusHalvingWindow [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      endpointRead midpointRead branchRead retainedRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg →
      Cont left right endpointRead →
        Cont endpointRead scale midpointRead →
          Cont midpointRead branch branchRead →
            Cont branchRead window retainedRead →
              Cont retainedRead endpoint realRead →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row left ∨ hsame row right ∨ hsame row scale ∨
                            hsame row midpoint ∨ hsame row branch ∨ hsame row window ∨
                              hsame row endpoint ∨ hsame row realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont left right endpointRead ∧
                            Cont endpointRead scale midpointRead ∧
                              Cont midpointRead branch branchRead ∧
                                Cont branchRead window retainedRead ∧
                                  Cont retainedRead endpoint realRead ∧
                                    hsame midpoint (append scale (append left right)) ∧
                                      PkgSig bundle realRead pkg)
                        hsame ∧ UnaryHistory retainedRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier endpointRoute midpointRoute branchRoute retainedRoute realRoute realPkg
  obtain ⟨leftUnary, rightUnary, scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    endpointUnary, midpointExact, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, _endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have midpointReadUnary : UnaryHistory midpointRead :=
    unary_cont_closed endpointReadUnary scaleUnary midpointRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed midpointReadUnary branchUnary branchRoute
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed branchReadUnary windowUnary retainedRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed retainedReadUnary endpointUnary realRoute
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
              hsame row branch ∨ hsame row window ∨ hsame row endpoint ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right endpointRead ∧
              Cont endpointRead scale midpointRead ∧ Cont midpointRead branch branchRead ∧
                Cont branchRead window retainedRead ∧ Cont retainedRead endpoint realRead ∧
                  hsame midpoint (append scale (append left right)) ∧
                    PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, midpointRoute, branchRoute, retainedRoute, realRoute,
          midpointExact, realPkg⟩
  }
  exact ⟨cert, retainedReadUnary, realReadUnary⟩

theorem DyadicMidpointDownstreamDyadicRatCorePackage [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      endpointRead midpointRead branchRead handoffRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg →
      Cont left right endpointRead →
        Cont endpointRead scale midpointRead →
          Cont midpointRead branch branchRead →
            Cont branchRead window handoffRead →
              Cont handoffRead provenance downstreamRead →
                PkgSig bundle downstreamRead pkg →
                  SemanticNameCert
                        (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row left ∨ hsame row right ∨ hsame row scale ∨
                            hsame row midpoint ∨ hsame row branch ∨ hsame row window ∨
                              hsame row provenance ∨ hsame row downstreamRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont left right endpointRead ∧
                            Cont endpointRead scale midpointRead ∧
                              Cont midpointRead branch branchRead ∧
                                Cont branchRead window handoffRead ∧
                                  Cont handoffRead provenance downstreamRead ∧
                                    PkgSig bundle downstreamRead pkg)
                        hsame ∧ UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier endpointRoute midpointRoute branchRoute handoffRoute downstreamRoute downstreamPkg
  obtain ⟨leftUnary, rightUnary, scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointExact, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, _endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have midpointReadUnary : UnaryHistory midpointRead :=
    unary_cont_closed endpointReadUnary scaleUnary midpointRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed midpointReadUnary branchUnary branchRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed branchReadUnary windowUnary handoffRoute
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed handoffReadUnary provenanceUnary downstreamRoute
  have sourceDownstream :
      (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row) downstreamRead := by
    exact ⟨hsame_refl downstreamRead, downstreamReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
              hsame row branch ∨ hsame row window ∨ hsame row provenance ∨
                hsame row downstreamRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right endpointRead ∧
              Cont endpointRead scale midpointRead ∧ Cont midpointRead branch branchRead ∧
                Cont branchRead window handoffRead ∧
                  Cont handoffRead provenance downstreamRead ∧
                    PkgSig bundle downstreamRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceDownstream
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, midpointRoute, branchRoute, handoffRoute,
          downstreamRoute, downstreamPkg⟩
  }
  exact ⟨cert, downstreamReadUnary⟩

end BEDC.Derived.DyadicMidpointUp

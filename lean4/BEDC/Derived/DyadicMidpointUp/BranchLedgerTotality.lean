import BEDC.Derived.DyadicMidpointUp

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMidpointBranchLedgerTotality [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert endpoint
      branchRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg ->
      Cont branch window branchRead -> Cont branchRead route ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
                hsame row branch ∨ hsame row window ∨ hsame row route ∨
                  hsame row endpoint ∨ hsame row branchRead ∨ hsame row ledgerRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont branch window branchRead ∧
                Cont branchRead route ledgerRead ∧ PkgSig bundle endpoint pkg ∧
                  PkgSig bundle ledgerRead pkg)
            hsame ∧ UnaryHistory branchRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: DyadicMidpointCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier branchRoute ledgerRoute ledgerPkg
  obtain ⟨_leftUnary, _rightUnary, _scaleUnary, _midpointUnary, branchUnary, windowUnary,
    _sameRowsUnary, routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointExact, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary windowUnary branchRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed branchReadUnary routeUnary ledgerRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row left ∨ hsame row right ∨ hsame row scale ∨ hsame row midpoint ∨
            hsame row branch ∨ hsame row window ∨ hsame row route ∨ hsame row endpoint ∨
              hsame row branchRead ∨ hsame row ledgerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont branch window branchRead ∧
            Cont branchRead route ledgerRead ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle ledgerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, branchRoute, ledgerRoute, endpointPkg, ledgerPkg⟩
  }
  exact ⟨cert, branchReadUnary, ledgerReadUnary⟩

end BEDC.Derived.DyadicMidpointUp

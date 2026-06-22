import BEDC.Derived.TaylorModelUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TaylorModelCarrier_remainder_obligation_route [AskSetup] [PackageSetup]
    {center jet subJet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint remainderRead obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelDisplayedFiniteJetSubwindow center jet subJet remainder ledger eval validated
      readback provenance nameCert sameRows route endpoint bundle pkg →
      Cont remainder ledger remainderRead →
        Cont remainderRead validated obligationRead →
          PkgSig bundle obligationRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row subJet ∨ hsame row remainder ∨ hsame row ledger ∨
                    hsame row remainderRead ∨ hsame row obligationRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont remainder ledger remainderRead ∧
                    Cont remainderRead validated obligationRead ∧
                      PkgSig bundle obligationRead pkg)
                hsame ∧
              UnaryHistory remainderRead ∧ UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro subwindow remainderRoute obligationRoute obligationPkg
  obtain ⟨carrier, _subJetUnary, _sameSubJet, _subJetPkg⟩ := subwindow
  obtain ⟨_centerUnary, _jetUnary, remainderUnary, ledgerUnary, _evalUnary,
    validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, _centerJetEval,
    _remainderLedgerReadback, _evalReadbackEndpoint, _endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have remainderReadUnary : UnaryHistory remainderRead :=
    unary_cont_closed remainderUnary ledgerUnary remainderRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed remainderReadUnary validatedUnary obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row subJet ∨ hsame row remainder ∨ hsame row ledger ∨
              hsame row remainderRead ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont remainder ledger remainderRead ∧
              Cont remainderRead validated obligationRead ∧ PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead ⟨hsame_refl obligationRead, obligationUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, remainderRoute, obligationRoute, obligationPkg⟩
  }
  exact ⟨cert, remainderReadUnary, obligationUnary⟩

theorem TaylorModelCarrier_validated_consumer_namecert_handoff [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint consumer publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg →
      Cont endpoint validated consumer →
        Cont consumer provenance publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row consumer ∨ hsame row provenance ∨ hsame row nameCert ∨
                    hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont endpoint validated consumer ∧
                    Cont consumer provenance publicRead ∧ PkgSig bundle publicRead pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
                        hsame ledger (append jet remainder) ∧
                          hsame eval (append center jet))
                hsame ∧
              UnaryHistory consumer ∧ UnaryHistory publicRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier consumerRoute publicRoute publicPkg
  have boundary :=
    TaylorModelCarrier_validated_consumer_boundary carrier consumerRoute
  obtain ⟨consumerUnary, ledgerRow, evalRow, provenancePkg, nameCertPkg⟩ := boundary
  obtain ⟨_centerUnary, _jetUnary, _remainderUnary, _ledgerUnary, _evalUnary,
    _validatedUnary, _readbackUnary, provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, _centerJetEval,
    _remainderLedgerReadback, _evalReadbackEndpoint, _endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerUnary provenanceUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumer ∨ hsame row provenance ∨ hsame row nameCert ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint validated consumer ∧
              Cont consumer provenance publicRead ∧ PkgSig bundle publicRead pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
                  hsame ledger (append jet remainder) ∧ hsame eval (append center jet))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, consumerRoute, publicRoute, publicPkg, provenancePkg,
          nameCertPkg, ledgerRow, evalRow⟩
  }
  exact ⟨cert, consumerUnary, publicUnary, provenancePkg, nameCertPkg⟩

end BEDC.Derived.TaylorModelUp

import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.TaylorModelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TaylorModelCarrier [AskSetup] [PackageSetup]
    (center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory jet ∧ UnaryHistory remainder ∧ UnaryHistory ledger ∧
    UnaryHistory eval ∧ UnaryHistory validated ∧ UnaryHistory readback ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ UnaryHistory sameRows ∧
        UnaryHistory route ∧ UnaryHistory endpoint ∧ hsame ledger (append jet remainder) ∧
          hsame eval (append center jet) ∧ Cont sameRows route endpoint ∧
            Cont center jet eval ∧ Cont remainder ledger readback ∧
              Cont eval readback endpoint ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

def TaylorModelDisplayedFiniteJetSubwindow [AskSetup] [PackageSetup]
    (center jet subJet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
      sameRows route endpoint bundle pkg ∧
    UnaryHistory subJet ∧ hsame subJet jet ∧ PkgSig bundle subJet pkg

theorem TaylorModelCarrier_interval_remainder_soundness [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint remainder' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      hsame remainder remainder' ->
        Cont remainder' ledger readback' ->
          Cont eval readback' endpoint ->
            UnaryHistory remainder' ∧ UnaryHistory readback' ∧ hsame readback readback' ∧
              UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameRemainder remainderLedgerReadback' evalReadbackEndpoint
  obtain ⟨centerUnary, jetUnary, remainderUnary, ledgerUnary, _evalUnary, _validatedUnary,
    _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary, _routeUnary,
    _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, evalRoute, readbackRoute,
    _endpointRoute, endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have remainderUnary' : UnaryHistory remainder' :=
    unary_transport remainderUnary sameRemainder
  have evalClosed : UnaryHistory eval :=
    unary_cont_closed centerUnary jetUnary evalRoute
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed remainderUnary' ledgerUnary remainderLedgerReadback'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameRemainder (hsame_refl ledger) readbackRoute
      remainderLedgerReadback'
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed evalClosed readbackUnary' evalReadbackEndpoint
  exact ⟨remainderUnary', readbackUnary', sameReadback, endpointUnary, endpointPkg⟩

theorem TaylorModelCarrier_validated_consumer_boundary [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      Cont endpoint validated consumer ->
        UnaryHistory consumer ∧ hsame ledger (append jet remainder) ∧
          hsame eval (append center jet) ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier consumerRoute
  obtain ⟨_centerUnary, _jetUnary, _remainderUnary, _ledgerUnary, _evalUnary,
    validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, endpointUnary, ledgerRow, evalRow, _sameRowsRoute, _evalRoute,
    _readbackRoute, _endpointRoute, _endpointPkg, provenancePkg, nameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary validatedUnary consumerRoute
  exact ⟨consumerUnary, ledgerRow, evalRow, provenancePkg, nameCertPkg⟩

theorem TaylorModelCarrier_seed_public_package [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      Cont endpoint validated consumer ->
        exists coefficientRead : BHist,
          UnaryHistory coefficientRead ∧ UnaryHistory consumer ∧
            hsame coefficientRead (append jet eval) ∧ hsame ledger (append jet remainder) ∧
              hsame eval (append center jet) ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier consumerRoute
  obtain ⟨_centerUnary, jetUnary, _remainderUnary, _ledgerUnary, evalUnary,
    validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, endpointUnary, ledgerRow, evalRow, _sameRowsRoute, _evalRoute,
    _readbackRoute, _endpointRoute, endpointPkg, provenancePkg, nameCertPkg⟩ := carrier
  let coefficientRead : BHist := append jet eval
  have coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed jetUnary evalUnary (rfl : Cont jet eval coefficientRead)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary validatedUnary consumerRoute
  exact ⟨coefficientRead, coefficientReadUnary, consumerUnary, rfl, ledgerRow, evalRow,
    endpointPkg, provenancePkg, nameCertPkg⟩

theorem TaylorModelCarrier_finite_jet_prefix_restriction [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint subJet subEval subEndpoint coefficientRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      hsame subJet jet ->
        Cont center subJet subEval ->
          Cont subEval readback subEndpoint ->
            Cont subEndpoint validated coefficientRead ->
              PkgSig bundle subEndpoint pkg ->
                UnaryHistory subJet ∧ UnaryHistory subEval ∧ UnaryHistory subEndpoint ∧
                  UnaryHistory coefficientRead ∧ hsame eval (append center jet) ∧
                    Cont center subJet subEval ∧ Cont subEval readback subEndpoint ∧
                      Cont subEndpoint validated coefficientRead ∧
                        PkgSig bundle subEndpoint pkg := by
  intro carrier sameSubJet centerSubJet subEvalReadback subEndpointValidated subEndpointPkg
  obtain ⟨centerUnary, jetUnary, _remainderUnary, _ledgerUnary, _evalUnary, validatedUnary,
    readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary, _routeUnary,
    _endpointUnary, _ledgerRow, evalRow, _sameRowsRoute, _centerJetEval,
    _remainderLedgerReadback, _evalReadbackEndpoint, _endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have subJetUnary : UnaryHistory subJet :=
    unary_transport jetUnary (hsame_symm sameSubJet)
  have subEvalUnary : UnaryHistory subEval :=
    unary_cont_closed centerUnary subJetUnary centerSubJet
  have subEndpointUnary : UnaryHistory subEndpoint :=
    unary_cont_closed subEvalUnary readbackUnary subEvalReadback
  have coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed subEndpointUnary validatedUnary subEndpointValidated
  exact
    ⟨subJetUnary, subEvalUnary, subEndpointUnary, coefficientReadUnary, evalRow,
      centerSubJet, subEvalReadback, subEndpointValidated, subEndpointPkg⟩

theorem TaylorModelRemainderObligationRoute [AskSetup] [PackageSetup]
    {center jet subJet remainder ledger eval validated readback provenance nameCert sameRows
      route endpoint subEval subEndpoint coefficientRead remainderRead obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelDisplayedFiniteJetSubwindow center jet subJet remainder ledger eval validated
        readback provenance nameCert sameRows route endpoint bundle pkg ->
      Cont center subJet subEval ->
        Cont subEval readback subEndpoint ->
          Cont subEndpoint validated coefficientRead ->
            Cont subJet remainder remainderRead ->
              Cont remainderRead ledger obligationRead ->
                PkgSig bundle obligationRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row center ∨ hsame row subJet ∨ hsame row remainder ∨
                          hsame row ledger ∨ hsame row subEval ∨ hsame row subEndpoint ∨
                            hsame row coefficientRead ∨ hsame row obligationRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont center subJet subEval ∧
                          Cont subEval readback subEndpoint ∧
                            Cont subEndpoint validated coefficientRead ∧
                              Cont subJet remainder remainderRead ∧
                                Cont remainderRead ledger obligationRead ∧
                                  PkgSig bundle obligationRead pkg)
                      hsame ∧
                    UnaryHistory obligationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro subwindow centerSubJet subEvalReadback subEndpointValidated subJetRemainder
    remainderLedger obligationPkg
  obtain ⟨carrier, subJetUnary, _sameSubJet, _subJetPkg⟩ := subwindow
  obtain ⟨centerUnary, _jetUnary, remainderUnary, ledgerUnary, _evalUnary, validatedUnary,
    readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary, _routeUnary,
    _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, _centerJetEval,
    _remainderLedgerReadback, _evalReadbackEndpoint, _endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have subEvalUnary : UnaryHistory subEval :=
    unary_cont_closed centerUnary subJetUnary centerSubJet
  have subEndpointUnary : UnaryHistory subEndpoint :=
    unary_cont_closed subEvalUnary readbackUnary subEvalReadback
  have _coefficientReadUnary : UnaryHistory coefficientRead :=
    unary_cont_closed subEndpointUnary validatedUnary subEndpointValidated
  have remainderReadUnary : UnaryHistory remainderRead :=
    unary_cont_closed subJetUnary remainderUnary subJetRemainder
  have obligationReadUnary : UnaryHistory obligationRead :=
    unary_cont_closed remainderReadUnary ledgerUnary remainderLedger
  have sourceObligation :
      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row) obligationRead := by
    exact ⟨hsame_refl obligationRead, obligationReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row center ∨ hsame row subJet ∨ hsame row remainder ∨ hsame row ledger ∨
              hsame row subEval ∨ hsame row subEndpoint ∨ hsame row coefficientRead ∨
                hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont center subJet subEval ∧
              Cont subEval readback subEndpoint ∧
                Cont subEndpoint validated coefficientRead ∧ Cont subJet remainder remainderRead ∧
                  Cont remainderRead ledger obligationRead ∧ PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead sourceObligation
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, centerSubJet, subEvalReadback, subEndpointValidated,
          subJetRemainder, remainderLedger, obligationPkg⟩
  }
  exact ⟨cert, obligationReadUnary⟩

theorem TaylorModelBridgeFacingRoute [AskSetup] [PackageSetup]
    {center jet subJet remainder ledger eval validated readback provenance nameCert sameRows
      route endpoint bridgeRead obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelDisplayedFiniteJetSubwindow center jet subJet remainder ledger eval validated
        readback provenance nameCert sameRows route endpoint bundle pkg ->
      Cont subJet remainder obligationRead ->
        Cont obligationRead endpoint bridgeRead ->
          PkgSig bundle bridgeRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row center ∨ hsame row subJet ∨ hsame row remainder ∨
                    hsame row ledger ∨ hsame row eval ∨ hsame row readback ∨
                      hsame row endpoint ∨ hsame row bridgeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont subJet remainder obligationRead ∧
                    Cont obligationRead endpoint bridgeRead ∧
                      PkgSig bundle bridgeRead pkg)
                hsame ∧
              UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro subwindow subJetRemainder obligationEndpoint bridgePkg
  obtain ⟨carrier, subJetUnary, _sameSubJet, _subJetPkg⟩ := subwindow
  obtain ⟨_centerUnary, _jetUnary, remainderUnary, _ledgerUnary, _evalUnary,
    _validatedUnary, _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary,
    _routeUnary, endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, _centerJetEval,
    _remainderLedgerReadback, _evalReadbackEndpoint, _endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have obligationReadUnary : UnaryHistory obligationRead :=
    unary_cont_closed subJetUnary remainderUnary subJetRemainder
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed obligationReadUnary endpointUnary obligationEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row center ∨ hsame row subJet ∨ hsame row remainder ∨
              hsame row ledger ∨ hsame row eval ∨ hsame row readback ∨
                hsame row endpoint ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont subJet remainder obligationRead ∧
              Cont obligationRead endpoint bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, subJetRemainder, obligationEndpoint, bridgePkg⟩
  }
  exact ⟨cert, bridgeReadUnary⟩

theorem TaylorModelCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {center jet remainder ledger eval validated readback provenance nameCert sameRows route
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TaylorModelCarrier center jet remainder ledger eval validated readback provenance nameCert
        sameRows route endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TaylorModelCarrier center jet remainder ledger eval validated readback provenance
                nameCert sameRows route endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            hsame row center ∨ hsame row jet ∨ hsame row remainder ∨ hsame row ledger ∨
              hsame row eval ∨ hsame row readback ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory endpoint ∧ Cont eval readback endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨centerUnary, jetUnary, remainderUnary, ledgerUnary, _evalUnary, _validatedUnary,
    _readbackUnary, _provenanceUnary, _nameCertUnary, _sameRowsUnary, _routeUnary,
    _endpointUnary, _ledgerRow, _evalRow, _sameRowsRoute, centerJetEval,
    remainderLedgerReadback, evalReadbackEndpoint, endpointPkg, _provenancePkg,
    _nameCertPkg⟩ := carrier
  have evalUnary : UnaryHistory eval :=
    unary_cont_closed centerUnary jetUnary centerJetEval
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed remainderUnary ledgerUnary remainderLedgerReadback
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed evalUnary readbackUnary evalReadbackEndpoint
  have sourceEndpoint :
      TaylorModelCarrier center jet remainder ledger eval validated readback provenance
          nameCert sameRows route endpoint bundle pkg ∧ hsame endpoint endpoint := by
    exact ⟨carrierWitness, hsame_refl endpoint⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            TaylorModelCarrier center jet remainder ledger eval validated readback provenance
                nameCert sameRows route endpoint bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist =>
            hsame row center ∨ hsame row jet ∨ hsame row remainder ∨ hsame row ledger ∨
              hsame row eval ∨ hsame row readback ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows'
        exact hsame_symm sameRows'
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows' sourceRow
        exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows') sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary, evalReadbackEndpoint, endpointPkg⟩

end BEDC.Derived.TaylorModelUp

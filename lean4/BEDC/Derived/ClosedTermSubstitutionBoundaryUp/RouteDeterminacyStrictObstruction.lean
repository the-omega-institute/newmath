import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.RootRouteBridgeDeterminacy

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRouteDeterminacyStrictObstruction [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootRoute rootRoute'
      obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route rootRoute ->
                Cont consumer route rootRoute' ->
                  Cont rootRoute ledger obstruction ->
                    PkgSig bundle obstruction pkg ->
                      hsame rootRoute rootRoute' ∧
                        SemanticNameCert
                            (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row route ∨ hsame row consumer ∨
                                hsame row rootRoute ∨ hsame row rootRoute' ∨
                                  hsame row obstruction)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont consumer route rootRoute ∧
                                Cont consumer route rootRoute' ∧
                                  Cont rootRoute ledger obstruction ∧
                                    PkgSig bundle obstruction pkg)
                            hsame ∧
                          UnaryHistory obstruction := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteRoot consumerRouteRoot' rootLedgerObstruction
    obstructionPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have rootUnary : UnaryHistory rootRoute :=
    unary_cont_closed consumerUnary routeUnary consumerRouteRoot
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerObstruction
  have sameRoot : hsame rootRoute rootRoute' :=
    cont_deterministic consumerRouteRoot consumerRouteRoot'
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row consumer ∨ hsame row rootRoute ∨
              hsame row rootRoute' ∨ hsame row obstruction)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont consumer route rootRoute ∧
              Cont consumer route rootRoute' ∧ Cont rootRoute ledger obstruction ∧
                PkgSig bundle obstruction pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obstruction ⟨hsame_refl obstruction, obstructionUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceData.left)))
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, consumerRouteRoot, consumerRouteRoot',
          rootLedgerObstruction, obstructionPkg⟩
  }
  exact ⟨sameRoot, cert, obstructionUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

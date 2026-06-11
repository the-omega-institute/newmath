import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootCompilerStrictLocalObstruction [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead handoff
      obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              Cont compilerRead ledger handoff ->
                Cont handoff route obstruction ->
                  PkgSig bundle obstruction pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row compilerRead ∨ hsame row handoff ∨ hsame row obstruction)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont compilerRead ledger handoff ∧
                            Cont handoff route obstruction ∧ PkgSig bundle obstruction pkg)
                        hsame ∧
                      UnaryHistory compilerRead ∧ UnaryHistory handoff ∧
                        UnaryHistory obstruction := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompiler compilerLedgerHandoff handoffRouteObstruction obstructionPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompiler
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed compilerUnary ledgerUnary compilerLedgerHandoff
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed handoffUnary routeUnary handoffRouteObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstruction ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compilerRead ∨ hsame row handoff ∨ hsame row obstruction)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compilerRead ledger handoff ∧
              Cont handoff route obstruction ∧ PkgSig bundle obstruction pkg)
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
      exact Or.inr (Or.inr sourceData.left)
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, compilerLedgerHandoff, handoffRouteObstruction,
          obstructionPkg⟩
  }
  exact ⟨cert, compilerUnary, handoffUnary, obstructionUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

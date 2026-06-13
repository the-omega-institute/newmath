import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootRouteStrictLocalObstruction [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit obstruction ->
              PkgSig bundle obstruction pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row obstruction)
                    (fun _row : BHist =>
                      Cont ledger audit route ∧ Cont route audit obstruction ∧
                        PkgSig bundle obstruction pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obstruction pkg)
                    hsame ∧
                  UnaryHistory route ∧ UnaryHistory obstruction := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditObstruction obstructionPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed routeUnary auditUnary routeAuditObstruction
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstruction)
          (fun _row : BHist =>
            Cont ledger audit route ∧ Cont route audit obstruction ∧ PkgSig bundle obstruction pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obstruction pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstruction (hsame_refl obstruction)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row _source
      exact ⟨ledgerAuditRoute, routeAuditObstruction, obstructionPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport obstructionUnary (hsame_symm source), obstructionPkg⟩
  }
  exact ⟨cert, routeUnary, obstructionUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

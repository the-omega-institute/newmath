import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootAuditGate [AskSetup] [PackageSetup]
    {source value depth shift substitution shiftRead substitutionRead ledger audit route
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitutionRead depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  PkgSig bundle rootRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                        (fun row : BHist => hsame row rootRead ∧ Cont route audit rootRead)
                        (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
                        hsame ∧
                      UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory rootRead ∧
                        Cont route audit rootRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead shiftSubstitutionLedger
    substitutionReadDepthAudit ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueShiftRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed shiftReadUnary depthUnary shiftReadDepthSubstitutionRead
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionReadUnary depthUnary substitutionReadDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row rootRead ∧ Cont route audit rootRead)
        (fun row : BHist => hsame row rootRead ∧ PkgSig bundle rootRead pkg)
        hsame := by
    exact
      { core :=
          { carrier_inhabited := Exists.intro rootRead
              (And.intro (hsame_refl rootRead) rootUnary)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro _row _row' sameRows
              exact hsame_symm sameRows
            equiv_trans := by
              intro _row _row' _row'' sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro row row' sameRows source
              exact
                And.intro
                  (hsame_trans (hsame_symm sameRows) source.left)
                  (unary_transport source.right sameRows) }
        pattern_sound := by
          intro row source
          exact And.intro source.left routeAuditRoot
        ledger_sound := by
          intro row source
          exact And.intro source.left rootPkg }
  exact ⟨cert, auditUnary, routeUnary, rootUnary, routeAuditRoot, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

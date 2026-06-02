import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootSubstitutionNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        UnaryHistory audit ->
          Cont ledger audit route ->
            UnaryHistory consumer ->
              Cont route consumer rootRead ->
                PkgSig bundle rootRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row value ∨ hsame row depth ∨
                          hsame row substitution ∨ hsame row ledger ∨ hsame row audit ∨
                            hsame row rootRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle rootRead pkg)
                      hsame ∧
                    UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro classifier shiftSubstitutionLedger auditUnary ledgerAuditRoute consumerUnary
    routeConsumerRoot rootPkg
  obtain ⟨sourceUnary, _valueUnary, _depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary consumerUnary routeConsumerRoot
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨
              hsame row substitution ∨ hsame row ledger ∨ hsame row audit ∨
                hsame row rootRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rootRead (And.intro (hsame_refl rootRead) rootUnary)
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
        intro _row _row' sameRows source
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro row source
      exact And.intro source.right rootPkg
  }
  exact And.intro cert rootUnary

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

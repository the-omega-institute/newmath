import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNamecertSourceLock [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont shift substitution ledger ->
              Cont substitution depth audit ->
                Cont ledger audit route ->
                  Cont audit route auditRead ->
                    PkgSig bundle auditRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row value ∨ hsame row sourceClosed ∨
                              hsame row valueClosed ∨ hsame row ledger ∨ hsame row auditRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont sourceClosed valueClosed ledger ∧
                              Cont shift substitution ledger ∧ PkgSig bundle auditRead pkg)
                          hsame ∧
                        UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                          UnaryHistory ledger ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro classifier sourceValueSourceClosed valueDepthValueClosed sourceClosedValueClosedLedger
    shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute auditRouteAuditRead
    auditReadPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueSourceClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthValueClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary sourceClosedValueClosedLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteAuditRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row sourceClosed ∨
              hsame row valueClosed ∨ hsame row ledger ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceClosed valueClosed ledger ∧
              Cont shift substitution ledger ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead (And.intro (hsame_refl auditRead) auditReadUnary)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro row source
      exact
        And.intro source.right
          (And.intro sourceClosedValueClosedLedger
            (And.intro shiftSubstitutionLedger auditReadPkg))
  }
  exact
    ⟨cert, sourceClosedUnary, valueClosedUnary, ledgerUnary, auditReadUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

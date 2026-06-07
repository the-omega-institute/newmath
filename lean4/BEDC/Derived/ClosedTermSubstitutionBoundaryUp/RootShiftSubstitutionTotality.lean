import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootShiftSubstitutionTotality [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route shiftRead substitutionRead rootRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  Cont rootRead ledger namedRead ->
                    PkgSig bundle namedRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row shift ∨ hsame row substitution ∨ hsame row ledger ∨
                              hsame row audit ∨ hsame row route ∨ hsame row rootRead ∨
                                hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont source value shiftRead ∧
                              Cont shiftRead depth substitutionRead ∧
                                Cont shift substitution ledger ∧
                                  Cont substitution depth audit ∧ Cont ledger audit route ∧
                                    Cont route audit rootRead ∧ Cont rootRead ledger namedRead ∧
                                      PkgSig bundle namedRead pkg)
                          hsame ∧
                        hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
    shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routeAuditRoot
    rootLedgerNamed namedPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    hsame_symm (cont_deterministic sourceValueShift sourceValueShiftRead)
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row shift ∨ hsame row substitution ∨ hsame row ledger ∨
              hsame row audit ∨ hsame row route ∨ hsame row rootRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source value shiftRead ∧
              Cont shiftRead depth substitutionRead ∧ Cont shift substitution ledger ∧
                Cont substitution depth audit ∧ Cont ledger audit route ∧
                  Cont route audit rootRead ∧ Cont rootRead ledger namedRead ∧
                    PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceValueShiftRead, shiftReadDepthSubstitutionRead,
          shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditRoot,
          rootLedgerNamed, namedPkg⟩
  }
  exact ⟨cert, sameShiftRead, sameSubstitutionRead, namedUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryPrimitiveLedgerScope [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route primitiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont ledger depth audit ->
          Cont audit ledger route ->
            Cont route audit primitiveRead ->
              PkgSig bundle primitiveRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row primitiveRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row value ∨ hsame row depth ∨
                        hsame row shift ∨ hsame row substitution ∨ hsame row ledger ∨
                          hsame row audit ∨ hsame row route ∨ hsame row primitiveRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont shift substitution ledger ∧
                        Cont ledger depth audit ∧ Cont audit ledger route ∧
                          Cont route audit primitiveRead ∧ PkgSig bundle primitiveRead pkg)
                    hsame ∧
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory primitiveRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger ledgerDepthAudit auditLedgerRoute routeAuditPrimitive
    primitivePkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed ledgerUnary depthUnary ledgerDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed auditUnary ledgerUnary auditLedgerRoute
  have primitiveUnary : UnaryHistory primitiveRead :=
    unary_cont_closed routeUnary auditUnary routeAuditPrimitive
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row primitiveRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row value ∨ hsame row depth ∨ hsame row shift ∨
              hsame row substitution ∨ hsame row ledger ∨ hsame row audit ∨
                hsame row route ∨ hsame row primitiveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont shift substitution ledger ∧ Cont ledger depth audit ∧
              Cont audit ledger route ∧ Cont route audit primitiveRead ∧
                PkgSig bundle primitiveRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro primitiveRead
        ⟨hsame_refl primitiveRead, primitiveUnary⟩
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
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, shiftSubstitutionLedger, ledgerDepthAudit, auditLedgerRoute,
          routeAuditPrimitive, primitivePkg⟩
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, primitiveUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

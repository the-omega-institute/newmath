import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryKernelScopePackage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer ledger scopeRead ->
                PkgSig bundle scopeRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        ClosedTermSubstitutionBoundaryClassifier source value depth shift
                          substitution ∧ hsame row scopeRead)
                      (fun row : BHist => Cont consumer ledger row ∧ PkgSig bundle scopeRead pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle scopeRead pkg)
                      hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory consumer ∧ UnaryHistory scopeRead ∧
                        Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                          Cont ledger audit route ∧ Cont route audit consumer ∧
                            Cont consumer ledger scopeRead ∧ PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerLedgerScope scopePkg
  have classifierWitness :
      ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution :=
    classifier
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
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed consumerUnary ledgerUnary consumerLedgerScope
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
            hsame row scopeRead)
        (fun row : BHist => Cont consumer ledger row ∧ PkgSig bundle scopeRead pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle scopeRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead
        (And.intro classifierWitness (hsame_refl scopeRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact And.intro
        (cont_result_hsame_transport consumerLedgerScope (hsame_symm source.right))
        scopePkg
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport scopeUnary (hsame_symm source.right)) scopePkg
  }
  exact
    ⟨cert, ledgerUnary, auditUnary, routeUnary, consumerUnary, scopeUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerLedgerScope, scopePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

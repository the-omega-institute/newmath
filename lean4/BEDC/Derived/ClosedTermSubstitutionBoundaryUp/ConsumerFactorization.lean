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

theorem ClosedTermSubstitutionBoundaryConsumerFactorization [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer factorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer route factorRead ->
                PkgSig bundle factorRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        ClosedTermSubstitutionBoundaryClassifier source value depth shift
                          substitution ∧ hsame row factorRead)
                      (fun row : BHist =>
                        Cont consumer route row ∧ Cont ledger audit route ∧
                          PkgSig bundle factorRead pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle factorRead pkg)
                      hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory consumer ∧ UnaryHistory factorRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerRouteFactor factorPkg
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
  have factorUnary : UnaryHistory factorRead :=
    unary_cont_closed consumerUnary routeUnary consumerRouteFactor
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ∧
              hsame row factorRead)
          (fun row : BHist =>
            Cont consumer route row ∧ Cont ledger audit route ∧ PkgSig bundle factorRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle factorRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro factorRead
        (And.intro classifierWitness (hsame_refl factorRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport consumerRouteFactor (hsame_symm source.right),
          ledgerAuditRoute, factorPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport factorUnary (hsame_symm source.right)) factorPkg
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, consumerUnary, factorUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

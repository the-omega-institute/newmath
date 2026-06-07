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

theorem ClosedTermSubstitutionBoundaryRootNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route root blocked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit root ->
              Cont root ledger blocked ->
                PkgSig bundle blocked pkg ->
                  SemanticNameCert (fun row : BHist => hsame row blocked ∧ UnaryHistory row)
                    (fun row : BHist => Cont root ledger blocked ∧ PkgSig bundle blocked pkg)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle blocked pkg)
                    hsame ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory root ∧ UnaryHistory blocked := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRoot rootLedgerBlocked blockedPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory root :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have blockedUnary : UnaryHistory blocked :=
    unary_cont_closed rootUnary ledgerUnary rootLedgerBlocked
  have cert :
      SemanticNameCert (fun row : BHist => hsame row blocked ∧ UnaryHistory row)
        (fun row : BHist => Cont root ledger blocked ∧ PkgSig bundle blocked pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle blocked pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro blocked
        (And.intro (hsame_refl blocked) blockedUnary)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row _source
      exact And.intro rootLedgerBlocked blockedPkg
    ledger_sound := by
      intro _row source
      exact And.intro source.right blockedPkg
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, rootUnary, blockedUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

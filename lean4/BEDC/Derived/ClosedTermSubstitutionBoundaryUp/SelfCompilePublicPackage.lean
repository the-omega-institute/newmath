import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.Derived.AuthorizedGeneratorRecursorUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySelfCompilePublicPackage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route closedRead : BHist}
    {signature eliminator motive branch descent output recAudit transport continuation provenance
      boundary localCert boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit closedRead ->
              AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output
                recAudit transport continuation provenance boundary localCert bundle pkg ->
                Cont boundary localCert boundaryRead ->
                  PkgSig bundle closedRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row closedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row closedRead ∧ Cont route audit closedRead ∧
                            Cont boundary localCert boundaryRead)
                        (fun row : BHist =>
                          hsame row closedRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle closedRead pkg)
                        hsame ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory closedRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditClosedRead recursorCarrier boundaryLocalCertRead closedReadPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    _outputUnary, _recAuditUnary, _transportUnary, _continuationUnary, provenanceUnary,
    boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportAuditContinuation, provenancePkg⟩ := recursorCarrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed routeUnary auditUnary routeAuditClosedRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryLocalCertRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedRead ∧ Cont route audit closedRead ∧
              Cont boundary localCert boundaryRead)
          (fun row : BHist =>
            hsame row closedRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle closedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closedRead
        (And.intro (hsame_refl closedRead) closedReadUnary)
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
      exact And.intro source.left (And.intro routeAuditClosedRead boundaryLocalCertRead)
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg closedReadPkg)
  }
  exact ⟨cert, ledgerUnary, auditUnary, routeUnary, closedReadUnary, boundaryReadUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.Derived.AuthorizedGeneratorRecursorUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryAuthorizedRecursorAuditRoute [AskSetup] [PackageSetup]
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
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory closedRead ∧ UnaryHistory boundaryRead ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit closedRead ∧
                          Cont boundary localCert boundaryRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditClosedRead recursorCarrier boundaryLocalCertRead
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
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, closedReadUnary, boundaryReadUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditClosedRead,
      boundaryLocalCertRead, provenancePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp

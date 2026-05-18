import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_audit_provenance_row [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      outputRead auditRead boundaryRead provenanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branches descent output audit
        transport routes provenance gap name bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead name auditRead ->
          Cont gap name boundaryRead ->
            Cont auditRead boundaryRead provenanceRead ->
              PkgSig bundle provenanceRead pkg ->
                UnaryHistory audit ∧ UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory provenanceRead ∧
                    hsame transport (append audit routes) ∧ Cont output audit outputRead ∧
                      Cont outputRead name auditRead ∧ Cont gap name boundaryRead ∧
                        Cont auditRead boundaryRead provenanceRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle provenanceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditOutputRead outputReadNameAuditRead gapNameBoundaryRead
    auditBoundaryProvenanceRead provenanceReadPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchesUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, routesUnary, provenanceUnary, gapUnary,
      nameUnary, _signatureEliminatorMotive, _motiveBranchesDescent, _descentOutputAudit,
      transportAuditRoutes, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary nameUnary outputReadNameAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed auditReadUnary boundaryReadUnary auditBoundaryProvenanceRead
  exact
    ⟨auditUnary, outputReadUnary, auditReadUnary, boundaryReadUnary, provenanceReadUnary,
      transportAuditRoutes, outputAuditOutputRead, outputReadNameAuditRead, gapNameBoundaryRead,
      auditBoundaryProvenanceRead, provenancePkg, provenanceReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

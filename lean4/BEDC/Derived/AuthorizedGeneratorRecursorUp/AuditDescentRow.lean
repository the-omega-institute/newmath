import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAuditDescentRow [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport route provenance boundary
      name descentRead auditRead provenanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport route provenance boundary name bundle pkg →
      Cont descent audit descentRead →
        Cont output audit auditRead →
          Cont descentRead auditRead provenanceRead →
            PkgSig bundle provenanceRead pkg →
              UnaryHistory descent ∧ UnaryHistory audit ∧ UnaryHistory descentRead ∧
                UnaryHistory auditRead ∧ UnaryHistory provenanceRead ∧
                  Cont descent audit descentRead ∧ Cont output audit auditRead ∧
                    Cont descentRead auditRead provenanceRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle provenanceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier descentAuditRead outputAuditRead descentAuditProvenance provenanceReadPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _boundaryUnary, _nameUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportAuditRoute, provenancePkg⟩ := carrier
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed descentUnary auditUnary descentAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed descentReadUnary auditReadUnary descentAuditProvenance
  exact
    ⟨descentUnary, auditUnary, descentReadUnary, auditReadUnary, provenanceReadUnary,
      descentAuditRead, outputAuditRead, descentAuditProvenance, provenancePkg,
      provenanceReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

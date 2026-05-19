import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchLedgerDisjointness [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont motive branch branchRead ->
        Cont branchRead descent output ->
          Cont output audit auditRead ->
            PkgSig bundle auditRead pkg ->
              UnaryHistory branch ∧ UnaryHistory branchRead ∧ UnaryHistory output ∧
                UnaryHistory auditRead ∧ Cont motive branch branchRead ∧
                  Cont branchRead descent output ∧ Cont output audit auditRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier motiveBranchRead branchReadDescentOutput outputAuditRead auditReadPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      _outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchRead
  have outputUnary : UnaryHistory output :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescentOutput
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  exact
    ⟨branchUnary, branchReadUnary, outputUnary, auditReadUnary, motiveBranchRead,
      branchReadDescentOutput, outputAuditRead, transportAuditContinuation, provenancePkg,
      auditReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootMotiveDescentStability [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N motiveRead branchRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont M B motiveRead ->
        Cont motiveRead D branchRead ->
          Cont branchRead A auditRead ->
            PkgSig bundle auditRead pkg ->
              UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory motiveRead ∧
                UnaryHistory branchRead ∧ UnaryHistory auditRead ∧ Cont I E M ∧
                  Cont M B motiveRead ∧ Cont motiveRead D branchRead ∧ Cont D O A ∧
                    Cont branchRead A auditRead ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier motiveBranchRead motiveDescentBranchRead branchAuditRead auditPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, transportUnary, continuationUnary, provenanceUnary, _boundaryUnary,
    _localCertUnary, signatureEliminatorMotive, _motiveBranchDescent, descentOutputAudit,
    transportAuditContinuation, provenancePkg⟩ := carrier
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary descentUnary motiveDescentBranchRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed branchReadUnary auditUnary branchAuditRead
  have _outputUnary : UnaryHistory O := outputUnary
  have _transportUnary : UnaryHistory H := transportUnary
  have _continuationUnary : UnaryHistory C := continuationUnary
  have _provenanceUnary : UnaryHistory P := provenanceUnary
  exact
    ⟨motiveUnary, branchUnary, descentUnary, motiveReadUnary, branchReadUnary, auditReadUnary,
      signatureEliminatorMotive, motiveBranchRead, motiveDescentBranchRead, descentOutputAudit,
      branchAuditRead, transportAuditContinuation, provenancePkg, auditPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorMotiveBranchTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N motiveRead branchRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont M B motiveRead ->
        Cont motiveRead D branchRead ->
          Cont branchRead O publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory D ∧
                UnaryHistory motiveRead ∧ UnaryHistory branchRead ∧ UnaryHistory publicRead ∧
                  Cont I E M ∧ Cont M B motiveRead ∧ Cont motiveRead D branchRead ∧
                    Cont D O A ∧ Cont branchRead O publicRead ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier motiveBranchRead motiveDescentBranchRead branchOutputPublic publicPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, signatureEliminatorMotive, _motiveBranchDescent,
    descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary descentUnary motiveDescentBranchRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary outputUnary branchOutputPublic
  exact
    ⟨motiveUnary, branchUnary, descentUnary, motiveReadUnary, branchReadUnary,
      publicReadUnary, signatureEliminatorMotive, motiveBranchRead, motiveDescentBranchRead,
      descentOutputAudit, branchOutputPublic, transportAuditContinuation, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

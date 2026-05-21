import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchMotivePairing [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N motiveRead branchRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I M motiveRead ->
        Cont motiveRead B branchRead ->
          Cont branchRead D outputRead ->
            PkgSig bundle outputRead pkg ->
              UnaryHistory I ∧ UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory D ∧
                UnaryHistory motiveRead ∧ UnaryHistory branchRead ∧
                  UnaryHistory outputRead ∧ Cont I M motiveRead ∧
                    Cont motiveRead B branchRead ∧ Cont branchRead D outputRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier signatureMotiveRead motiveReadBranch branchReadDescent outputPkg
  obtain ⟨signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    _outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed signatureUnary motiveUnary signatureMotiveRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchUnary motiveReadBranch
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescent
  exact
    ⟨signatureUnary, motiveUnary, branchUnary, descentUnary, motiveReadUnary,
      branchReadUnary, outputReadUnary, signatureMotiveRead, motiveReadBranch,
      branchReadDescent, transportAuditContinuation, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

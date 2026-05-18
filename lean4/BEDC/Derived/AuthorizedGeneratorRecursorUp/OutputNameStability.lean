import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputNameStability [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead publicRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C publicRead ->
          Cont publicRead N stableRead ->
            PkgSig bundle stableRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory outputRead ∧
                UnaryHistory publicRead ∧ UnaryHistory stableRead ∧
                  hsame H (append A C) ∧ Cont O A outputRead ∧
                    Cont outputRead C publicRead ∧ Cont publicRead N stableRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier outputAuditRead outputContinuationPublic publicNameStable stablePkg
  obtain ⟨_inputUnary, _elimUnary, _motiveUnary, _branchUnary, _descentUnary, outputUnary,
    auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
    localCertUnary, _inputElimMotive, _motiveBranchDescent, _descentOutputAudit,
    transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary continuationUnary outputContinuationPublic
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed publicReadUnary localCertUnary publicNameStable
  exact
    ⟨outputUnary, auditUnary, outputReadUnary, publicReadUnary, stableReadUnary,
      transportAuditContinuation, outputAuditRead, outputContinuationPublic, publicNameStable,
      provenancePkg, stablePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

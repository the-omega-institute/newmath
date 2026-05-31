import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCompletionBoundaryExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead G boundaryRead ->
          Cont boundaryRead N completionRead ->
            Cont completionRead C publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory N ∧
                  UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory publicRead ∧
                      Cont O A outputRead ∧ Cont outputRead G boundaryRead ∧
                        Cont boundaryRead N completionRead ∧
                          Cont completionRead C publicRead ∧ hsame H (append A C) ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputBoundaryRead boundaryNameCompletion
    completionContinuationPublic publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, nameUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, auditContinuationSame, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputReadUnary boundaryUnary outputBoundaryRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryReadUnary nameUnary boundaryNameCompletion
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed completionReadUnary continuationUnary completionContinuationPublic
  exact
    ⟨outputUnary, auditUnary, boundaryUnary, nameUnary, outputReadUnary, boundaryReadUnary,
      completionReadUnary, publicReadUnary, outputAuditRead, outputBoundaryRead,
      boundaryNameCompletion, completionContinuationPublic, auditContinuationSame, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

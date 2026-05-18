import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootAuditHandoffLock [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead publicRead outputRead auditRead boundaryRead
      lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead C publicRead ->
          Cont O A outputRead ->
            Cont outputRead N auditRead ->
              Cont G N boundaryRead ->
                Cont auditRead boundaryRead lockedRead ->
                  PkgSig bundle lockedRead pkg ->
                    UnaryHistory publicRead ∧ UnaryHistory auditRead ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory lockedRead ∧
                        Cont B D branchRead ∧ Cont branchRead C publicRead ∧
                          Cont O A outputRead ∧ Cont outputRead N auditRead ∧
                            Cont G N boundaryRead ∧ Cont auditRead boundaryRead lockedRead ∧
                              hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle lockedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchDescentRead branchContinuationPublic outputAuditRead outputNameAuditRead
    gapNameBoundaryRead auditBoundaryLocked lockedPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, transportUnary, continuationUnary, provenanceUnary, boundaryUnary,
    localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
    transportAuditContinuation, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary continuationUnary branchContinuationPublic
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary localCertUnary outputNameAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary gapNameBoundaryRead
  have lockedReadUnary : UnaryHistory lockedRead :=
    unary_cont_closed auditReadUnary boundaryReadUnary auditBoundaryLocked
  have _transportUnary : UnaryHistory H := transportUnary
  have _provenanceUnary : UnaryHistory P := provenanceUnary
  exact
    ⟨publicReadUnary, auditReadUnary, boundaryReadUnary, lockedReadUnary, branchDescentRead,
      branchContinuationPublic, outputAuditRead, outputNameAuditRead, gapNameBoundaryRead,
      auditBoundaryLocked, transportAuditContinuation, provenancePkg, lockedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

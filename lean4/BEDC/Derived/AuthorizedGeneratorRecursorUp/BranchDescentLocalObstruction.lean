import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchDescentLocalObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead auditRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont M D descentRead ->
          Cont O A outputRead ->
            Cont outputRead N auditRead ->
              Cont G N boundaryRead ->
                UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                  UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory boundaryRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier branchRoute descentRoute outputRoute auditRoute boundaryRoute
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportSame, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary descentUnary descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary localCertUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryRoute
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, auditReadUnary,
      boundaryReadUnary, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

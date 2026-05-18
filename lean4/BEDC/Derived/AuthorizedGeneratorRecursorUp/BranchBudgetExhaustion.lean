import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchBudgetExhaustion
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D branchRead →
        Cont branchRead M descentRead →
          Cont descentRead O outputRead →
            UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
              UnaryHistory outputRead ∧ Cont B D branchRead ∧
                Cont branchRead M descentRead ∧ Cont descentRead O outputRead ∧
                  hsame H (append A C) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier branchRoute descentRoute outputRoute
  have branchUnary : UnaryHistory B := carrier.right.right.right.left
  have descentUnary : UnaryHistory D := carrier.right.right.right.right.left
  have motiveUnary : UnaryHistory M := carrier.right.right.left
  have outputUnary : UnaryHistory O := carrier.right.right.right.right.right.left
  have transportSame : hsame H (append A C) :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary motiveUnary descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary outputRoute
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, branchRoute, descentRoute, outputRoute,
      transportSame, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp

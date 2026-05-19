import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealCompletionExactBoundaryTerminalSealDeterminacy [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N L' K' J' S' W' R' D' E' H' C' P' N'
      budgetRead budgetRead' terminalRead terminalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame W W' →
      hsame R R' →
        hsame D D' →
          hsame E E' →
            Cont W R budgetRead →
              Cont W' R' budgetRead' →
                Cont D E terminalRead →
                  Cont D' E' terminalRead' →
                    PkgSig bundle terminalRead pkg →
                      PkgSig bundle terminalRead' pkg →
                        hsame budgetRead budgetRead' ∧ hsame terminalRead terminalRead' ∧
                          PkgSig bundle terminalRead pkg ∧
                            PkgSig bundle terminalRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro sameW sameR sameD sameE budgetRoute budgetRoute' terminalRoute terminalRoute'
    terminalPkg terminalPkg'
  have sameBudgetRead : hsame budgetRead budgetRead' :=
    cont_respects_hsame sameW sameR budgetRoute budgetRoute'
  have sameTerminalRead : hsame terminalRead terminalRead' :=
    cont_respects_hsame sameD sameE terminalRoute terminalRoute'
  exact ⟨sameBudgetRead, sameTerminalRead, terminalPkg, terminalPkg'⟩

end BEDC.Derived.RealCompletionExactBoundaryUp

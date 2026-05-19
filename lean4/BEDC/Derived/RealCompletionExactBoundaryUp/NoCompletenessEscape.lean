import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealCompletionExactBoundaryNoCompletenessEscape [AskSetup] [PackageSetup]
    {D E terminalRead escape : BHist} :
    Cont D E terminalRead -> Cont terminalRead (BHist.e1 escape) D -> False := by
  -- BEDC touchpoint anchor: BHist Cont AskSetup PackageSetup
  intro terminalRoute escapeRoute
  have escapedSource : Cont D (append E (BHist.e1 escape)) D := by
    cases terminalRoute
    exact cont_intro (escapeRoute.trans (append_assoc D E (BHist.e1 escape)))
  have emptyVisibleTail : hsame (append E (BHist.e1 escape)) BHist.Empty :=
    cont_right_unit_unique escapedSource
  exact not_hsame_e1_empty (append_eq_empty_iff.mp emptyVisibleTail).right

end BEDC.Derived.RealCompletionExactBoundaryUp

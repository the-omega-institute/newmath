import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.HausdorffMomentProblemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def HausdorffMomentProblemCarrier (M I R P V Q L S T C G N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  hsame S S ∧ Cont T M Q ∧ hsame I I ∧ hsame R R ∧ hsame P P ∧ hsame V V ∧
    hsame L L ∧ hsame C C ∧ hsame G G ∧ hsame N N

theorem HausdorffMomentProblemCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M I R P V Q L S T C G N : BHist}
    (h : HausdorffMomentProblemCarrier M I R P V Q L S T C G N) :
    HausdorffMomentProblemCarrier M I R P V Q L S T C G N ∧ hsame S S ∧ hsame C C ∧
      hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame AskSetup PackageSetup
  have carrier := h
  obtain ⟨support, _windowRoute, _interval, _readback, _polynomial, _positivity,
    _localizing, terminalSeal, _handoff, localName⟩ := h
  exact ⟨carrier, support, terminalSeal, localName⟩

end BEDC.Derived.HausdorffMomentProblemUp

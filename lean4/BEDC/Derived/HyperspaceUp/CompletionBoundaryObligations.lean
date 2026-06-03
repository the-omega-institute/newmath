import BEDC.Derived.HyperspaceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem HyperspaceCompletionBoundaryObligations (H : HyperspaceUp) :
    ∃ X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist,
      H = HyperspaceUp.mk X K0 K1 N0 N1 D0 D1 R Hs C P M ∧
      Cont X K0 (append X K0) ∧
      Cont D0 D1 (append D0 D1) ∧
      hsame (BHist.e1 R) (BHist.e1 R) := by
  -- BEDC touchpoint anchor: BHist Cont append hsame
  cases H with
  | mk X K0 K1 N0 N1 D0 D1 R Hs C P M =>
      exact
        ⟨X, K0, K1, N0, N1, D0, D1, R, Hs, C, P, M,
          rfl,
          rfl,
          rfl,
          hsame_refl (BHist.e1 R)⟩

end BEDC.Derived.HyperspaceUp

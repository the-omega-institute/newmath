import BEDC.FKernel.Cont

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem DyadicTailBallWindowStability
    {B D F R H C P N D' F' H' C' P' N' oldRead newRead : BHist} :
    Cont D F oldRead →
      Cont D' F' newRead →
        hsame oldRead newRead →
          hsame P' N' →
            Cont D' F' oldRead ∧ hsame newRead oldRead ∧ hsame P' N' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro oldRoute newRoute sameRead sameName
  have oldOnNewWindow : Cont D' F' oldRead :=
    cont_result_hsame_transport newRoute (hsame_symm sameRead)
  exact ⟨oldOnNewWindow, hsame_symm sameRead, sameName⟩

end BEDC.Derived.DyadicTailBallUp

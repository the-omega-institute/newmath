import BEDC.Derived.PredictiveDescentUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.PredictiveDescentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Meta.TasteGate

theorem PredictiveDescentCarrier_nonescape
    {F O K A S X H C P N F' O' K' A' S' X' H' C' P' N' opRead scopeRead : BHist}
    (heq :
      predictiveDescentToEventFlow (PredictiveDescentUp.mk F O K A S X H C P N) =
        predictiveDescentToEventFlow (PredictiveDescentUp.mk F' O' K' A' S' X' H' C'
          P' N'))
    (hop : Cont O A opRead) (hscope : Cont A K scopeRead) :
    hsame O O' ∧ hsame K K' ∧ hsame A A' ∧ hsame S S' ∧ hsame X X' ∧
      Cont O' A' opRead ∧ Cont A' K' scopeRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  have hmk :
      PredictiveDescentUp.mk F O K A S X H C P N =
        PredictiveDescentUp.mk F' O' K' A' S' X' H' C' P' N' := by
    by_cases hp :
        PredictiveDescentUp.mk F O K A S X H C P N =
          PredictiveDescentUp.mk F' O' K' A' S' X' H' C' P' N'
    · exact hp
    · have hsep :=
        ChapterTasteGate.layer_separation
          (x := PredictiveDescentUp.mk F O K A S X H C P N)
          (y := PredictiveDescentUp.mk F' O' K' A' S' X' H' C' P' N')
          hp
      exact False.elim (hsep heq)
  cases hmk
  exact
    ⟨hsame_refl O, hsame_refl K, hsame_refl A, hsame_refl S, hsame_refl X,
      hop, hscope⟩

end BEDC.Derived.PredictiveDescentUp

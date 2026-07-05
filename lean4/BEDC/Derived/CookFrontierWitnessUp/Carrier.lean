import BEDC.Derived.CookFrontierWitnessUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CookFrontierWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def CookFrontierWitnessCarrier (_F M Y R T A _O H _C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  Cont M Y R ∧ Cont R T A ∧ hsame H H ∧ hsame P P ∧ hsame N N

theorem CookFrontierWitnessCarrier_staged_replay
    {F M Y R T A O H C P N : BHist} :
    CookFrontierWitnessCarrier F M Y R T A O H C P N →
      Cont M (append Y T) A ∧ hsame H H ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier
  obtain ⟨stageMY, stageRT, sameH, sameP, sameN⟩ := carrier
  constructor
  · cases stageMY
    cases stageRT
    exact cont_intro (append_assoc M Y T)
  · exact ⟨sameH, sameP, sameN⟩

end BEDC.Derived.CookFrontierWitnessUp

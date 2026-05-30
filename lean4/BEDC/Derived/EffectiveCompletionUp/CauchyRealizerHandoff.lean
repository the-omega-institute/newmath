import BEDC.Derived.EffectiveCompletionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.EffectiveCompletionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem EffectiveCompletionCauchyRealizerHandoff
    {x : EffectiveCompletionUp}
    {sourceRealizer representedWindow toleranceRead readbackRead realSealRead
      consumerRead : BHist} :
    Cont x.E x.Q sourceRealizer →
      Cont sourceRealizer x.K representedWindow →
        Cont representedWindow x.D toleranceRead →
          Cont toleranceRead x.R readbackRead →
            Cont readbackRead x.A realSealRead →
              Cont realSealRead x.U consumerRead →
                effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow x) =
                  some x ∧
                  Cont x.E x.Q sourceRealizer ∧
                    Cont sourceRealizer x.K representedWindow ∧
                      Cont representedWindow x.D toleranceRead ∧
                        Cont toleranceRead x.R readbackRead ∧
                          Cont readbackRead x.A realSealRead ∧
                            Cont realSealRead x.U consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont
  intro sourceRoute representedRoute toleranceRoute readbackRoute realSealRoute consumerRoute
  constructor
  · exact
      (EffectiveCompletionTasteGate_single_carrier_alignment).right.right.right.right.left x
  · exact
      ⟨sourceRoute, representedRoute, toleranceRoute, readbackRoute, realSealRoute,
        consumerRoute⟩

end BEDC.Derived.EffectiveCompletionUp

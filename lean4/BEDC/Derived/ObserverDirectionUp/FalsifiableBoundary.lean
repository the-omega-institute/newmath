import BEDC.Derived.ObserverDirectionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ObserverDirectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ObserverDirectionFalsifiableBoundary
    {R T U Urev L B H C P N oriented reversed : BHist} :
    U ≠ Urev ->
      Cont R T oriented ->
        Cont T R reversed ->
          hsame L L ->
            ObserverDirectionUp.mk R T U L B H C P N ≠
              ObserverDirectionUp.mk R T Urev L B H C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro separated _orientedRoute _reversedRoute _ledgerSelf samePacket
  exact separated (ObserverDirectionUp.mk.inj samePacket).right.right.left

end BEDC.Derived.ObserverDirectionUp

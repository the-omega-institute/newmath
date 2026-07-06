import BEDC.FKernel.Cont

namespace BEDC.Derived.AxisNatReplacementRefusalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem AxisNatReplacementRefusalCarrier_vision_realization
    {A _N B K H _C _P _L bridgeRead refusalRead publicRead : BHist} :
    Cont A B bridgeRead →
      Cont bridgeRead K refusalRead →
        Cont refusalRead H publicRead →
          hsame publicRead (append A (append B (append K H))) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro bridgeRoute refusalRoute publicRoute
  cases bridgeRoute
  cases refusalRoute
  cases publicRoute
  exact
    (append_assoc (append A B) K H).trans
      (append_assoc A B (append K H))

end BEDC.Derived.AxisNatReplacementRefusalUp

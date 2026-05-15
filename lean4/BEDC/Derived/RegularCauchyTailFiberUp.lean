import BEDC.Derived.RegularCauchyTailFiberUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.RegularCauchyTailFiberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RegularCauchyTailFiber_shared_fiber_route_changes_packet
    (R0 R1 W0 W1 D0 D1 T T' A H C P N : BHist)
    (_route : Cont T A C) (_route' : Cont T' A C) (hT : T ≠ T') :
    RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N ≠
      RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T' A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hpacket
  injection hpacket with _ _ _ _ _ _ hShared _ _ _ _ _
  exact hT hShared

theorem RegularCauchyTailFiberWindowProjection_changes_packet
    (R0 R1 W0 W0' W1 D0 D1 T A H C P N : BHist) (hW0 : W0 ≠ W0') :
    RegularCauchyTailFiberUp.mk R0 R1 W0 W1 D0 D1 T A H C P N ≠
      RegularCauchyTailFiberUp.mk R0 R1 W0' W1 D0 D1 T A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hpacket
  injection hpacket with _ _ hWindow _ _ _ _ _ _ _ _ _
  exact hW0 hWindow

end BEDC.Derived.RegularCauchyTailFiberUp

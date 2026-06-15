import BEDC.Derived.IntervalBisectionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.IntervalBisectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem IntervalBisectionCarrier_nested_cell_handoff
    (I M L R D S Q E H C P N : BHist) :
    Cont I M (append I M) ∧
      Cont L R (append L R) ∧
      intervalBisectionFromEventFlow
          (intervalBisectionToEventFlow
            (IntervalBisectionUp.mk I M L R D S Q E H C P N)) =
        some (IntervalBisectionUp.mk I M L R D S Q E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  exact
    ⟨rfl,
      rfl,
      IntervalBisectionTasteGate_single_carrier_alignment.right.left
        (IntervalBisectionUp.mk I M L R D S Q E H C P N)⟩

theorem IntervalBisectionObligationCarrier (I M L R D S Q E H C P N : BHist) :
    intervalBisectionFromEventFlow
        (intervalBisectionToEventFlow (IntervalBisectionUp.mk I M L R D S Q E H C P N)) =
      some (IntervalBisectionUp.mk I M L R D S Q E H C P N) ∧
      Cont I M (append I M) ∧ Cont L R (append L R) := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  exact
    ⟨IntervalBisectionTasteGate_single_carrier_alignment.right.left
        (IntervalBisectionUp.mk I M L R D S Q E H C P N),
      rfl,
      rfl⟩

end BEDC.Derived.IntervalBisectionUp

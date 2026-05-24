import BEDC.Derived.LocatedCutUp.CarrierAlignment
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

instance locatedCutBHistCarrier : BHistCarrier LocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCutToEventFlow
  fromEventFlow := locatedCutFromEventFlow

instance locatedCutChapterTasteGate : ChapterTasteGate LocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCutFromEventFlow (locatedCutToEventFlow x) = some x
    exact LocatedCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCutTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate LocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCutChapterTasteGate

end BEDC.Derived.LocatedCutUp

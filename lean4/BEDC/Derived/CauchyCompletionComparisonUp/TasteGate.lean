import BEDC.Derived.CauchyCompletionComparisonUp.CarrierAlignment
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

instance cauchyCompletionComparisonBHistCarrier : BHistCarrier CauchyCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionComparisonToEventFlow
  fromEventFlow := cauchyCompletionComparisonFromEventFlow

instance cauchyCompletionComparisonChapterTasteGate :
    ChapterTasteGate CauchyCompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionComparisonFromEventFlow (cauchyCompletionComparisonToEventFlow x) =
        some x
    exact CauchyCompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionComparisonTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionComparisonChapterTasteGate

end BEDC.Derived.CauchyCompletionComparisonUp

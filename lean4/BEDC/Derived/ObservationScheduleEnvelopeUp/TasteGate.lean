import BEDC.Derived.ObservationScheduleEnvelopeUp

namespace BEDC.Derived.ObservationScheduleEnvelopeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate
open BEDC.Derived.ObservationScheduleEnvelopeUp

theorem ObservationScheduleEnvelopeNameCert_obligations :
    (∀ x : ObservationScheduleEnvelopeUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ x y : ObservationScheduleEnvelopeUp,
        x ≠ y → BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y) ∧
        (∀ x y : ObservationScheduleEnvelopeUp,
          FieldFaithful.fields x = FieldFaithful.fields y → x = y) ∧
          (∃ x y : ObservationScheduleEnvelopeUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact ChapterTasteGate.round_trip x
  · constructor
    · intro x y hxy
      exact ChapterTasteGate.layer_separation x y hxy
    · constructor
      · intro x y hfields
        exact FieldFaithful.field_faithful x y hfields
      · exact
          ⟨ObservationScheduleEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            ObservationScheduleEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩

end BEDC.Derived.ObservationScheduleEnvelopeUp.TasteGate

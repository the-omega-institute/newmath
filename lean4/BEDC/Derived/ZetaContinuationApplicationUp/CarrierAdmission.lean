import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem ZetaContinuationApplicationCarrierAdmission (x : ZetaContinuationApplicationUp) :
    BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
      exists eta functional pole zeroLedger gamma application transport replay provenance name :
          BHist,
        x =
            ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application
              transport replay provenance name ∧
          zetaContinuationApplicationToEventFlow x =
            zetaContinuationApplicationToEventFlow
              (ZetaContinuationApplicationUp.mk eta functional pole zeroLedger gamma application
                transport replay provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ChapterTasteGate.round_trip x
  · cases x with
    | mk eta functional pole zeroLedger gamma application transport replay provenance name =>
        exact
          ⟨eta, functional, pole, zeroLedger, gamma, application, transport, replay, provenance,
            name, rfl, rfl⟩

end BEDC.Derived.ZetaContinuationApplicationUp

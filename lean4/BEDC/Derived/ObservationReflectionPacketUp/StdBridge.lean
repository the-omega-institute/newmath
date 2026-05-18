import BEDC.Derived.ObservationReflectionPacketUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ObservationReflectionPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem ObservationReflectionPacketUp_StdBridge :
    (∀ x : ObservationReflectionPacketUp,
      ∃ S H Sigma C P L E T R N : BHist,
        x = ObservationReflectionPacketUp.mk S H Sigma C P L E T R N ∧
          FieldFaithful.fields x = [S, H, Sigma, C, P, L, E, T, R, N] ∧
            BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
              hsame N N) ∧
      (∀ S H Sigma C P L E T R N : BHist,
        Cont C P (append C P) ∧ hsame (append C P) (append C P)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful ChapterTasteGate
  constructor
  · intro x
    cases x with
    | mk S H Sigma C P L E T R N =>
        exact
          ⟨S, H, Sigma, C, P, L, E, T, R, N, rfl, rfl,
            ChapterTasteGate.round_trip
              (ObservationReflectionPacketUp.mk S H Sigma C P L E T R N),
            hsame_refl N⟩
  · intro S H Sigma C P L E T R N
    exact ⟨rfl, hsame_refl (append C P)⟩

end BEDC.Derived.ObservationReflectionPacketUp

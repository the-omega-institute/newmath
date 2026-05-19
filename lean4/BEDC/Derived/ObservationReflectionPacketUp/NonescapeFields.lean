import BEDC.Derived.ObservationReflectionPacketUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ObservationReflectionPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ObservationReflectionPacket_nonescape_fields (x : ObservationReflectionPacketUp) :
    ∃ S H Sigma C P L E T R N : BHist,
      x = ObservationReflectionPacketUp.mk S H Sigma C P L E T R N ∧
        observationReflectionPacketFields x = [S, H, Sigma, C, P, L, E, T, R, N] ∧
          Cont S H (append S H) ∧ Cont Sigma C (append Sigma C) ∧
            hsame (append S H) (append S H) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk S H Sigma C P L E T R N =>
      exact ⟨S, H, Sigma, C, P, L, E, T, R, N, rfl, rfl, rfl, rfl, hsame_refl (append S H)⟩

end BEDC.Derived.ObservationReflectionPacketUp

import BEDC.Derived.SocketKindClassifierUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SocketKindClassifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem SocketKindClassifierUp_StdBridge (x : SocketKindClassifierUp) :
    ∃ S KD R G H C P N : BHist,
      x = SocketKindClassifierUp.mk S KD R G H C P N ∧
        FieldFaithful.fields x = [S, KD, R, G, H, C, P, N] ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
            Cont C P (append C P) ∧ hsame (append C P) (append C P) := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful BHistCarrier
  cases x with
  | mk S KD R G H C P N =>
      exact
        ⟨S, KD, R, G, H, C, P, N, rfl, rfl,
          ChapterTasteGate.round_trip (SocketKindClassifierUp.mk S KD R G H C P N),
          rfl, hsame_refl (append C P)⟩

end BEDC.Derived.SocketKindClassifierUp

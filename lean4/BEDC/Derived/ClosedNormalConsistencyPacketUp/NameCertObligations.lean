import BEDC.Derived.ClosedNormalConsistencyPacketUp.TasteGate
import BEDC.FKernel.Hist

namespace BEDC.Derived.ClosedNormalConsistencyPacketUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem ClosedNormalConsistencyPacketNameCertObligations
    (x : ClosedNormalConsistencyPacketUp) :
    ∃ L T B F K G H C P N : BHist,
      x = ClosedNormalConsistencyPacketUp.mk L T B F K G H C P N ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist L) (BHistCarrier.toEventFlow x) ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist T) (BHistCarrier.toEventFlow x) ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist B) (BHistCarrier.toEventFlow x) ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist F) (BHistCarrier.toEventFlow x) ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist K) (BHistCarrier.toEventFlow x) ∧
        List.Mem (closedNormalConsistencyPacketEncodeBHist G) (BHistCarrier.toEventFlow x) ∧
        hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark hsame BHistCarrier
  cases x with
  | mk L T B F K G H C P N =>
      exact
        ⟨L, T, B, F, K, G, H, C, P, N, rfl,
          List.Mem.head _,
          List.Mem.tail _ (List.Mem.head _),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _)))),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
          hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩

end BEDC.Derived.ClosedNormalConsistencyPacketUp

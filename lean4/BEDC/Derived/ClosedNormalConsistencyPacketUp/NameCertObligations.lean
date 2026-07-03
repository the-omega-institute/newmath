import BEDC.Derived.ClosedNormalConsistencyPacketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.ClosedNormalConsistencyPacketUp

open BEDC.FKernel.Cont
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

theorem ClosedNormalConsistencyPacketCarrier_normal_fragment_boundary
    {L T B F K G H C P N closedRead normalRead positiveRead transportedRead : BHist}
    (x : ClosedNormalConsistencyPacketUp)
    (hx : x = ClosedNormalConsistencyPacketUp.mk L T B F K G H C P N)
    (closedTyping : Cont L T closedRead)
    (normalFalse : Cont B F normalRead)
    (positiveFragment : Cont closedRead normalRead positiveRead)
    (transported : Cont positiveRead H transportedRead)
    (checkedReadback : hsame K positiveRead) :
    hsame transportedRead (append (append (append L T) (append B F)) H) ∧
      hsame K (append (append L T) (append B F)) ∧
      List.Mem (closedNormalConsistencyPacketEncodeBHist G)
        (BHistCarrier.toEventFlow x) ∧
      hsame G G := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame BHistCarrier
  cases hx
  cases closedTyping
  cases normalFalse
  cases positiveFragment
  cases transported
  cases checkedReadback
  exact
    ⟨rfl,
      rfl,
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))),
      hsame_refl G⟩

theorem ClosedNormalConsistencyPacketCarrier_subject_reduction_gap_boundary
    {L T B F K G H C P N closedRead normalRead positiveRead obstructionRead
      namedRead : BHist}
    (x : ClosedNormalConsistencyPacketUp)
    (hx : x = ClosedNormalConsistencyPacketUp.mk L T B F K G H C P N)
    (closedTyping : Cont L T closedRead)
    (normalFalse : Cont B F normalRead)
    (positiveFragment : Cont closedRead normalRead positiveRead)
    (obstructionRoute : Cont positiveRead G obstructionRead)
    (nameRoute : Cont obstructionRead N namedRead) :
    List.Mem (closedNormalConsistencyPacketEncodeBHist G)
        (BHistCarrier.toEventFlow x) ∧
      hsame namedRead (append (append (append (append L T) (append B F)) G) N) ∧
      hsame G G := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame BHistCarrier
  cases hx
  cases closedTyping
  cases normalFalse
  cases positiveFragment
  cases obstructionRoute
  cases nameRoute
  exact
    ⟨List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))),
      rfl,
      hsame_refl G⟩

end BEDC.Derived.ClosedNormalConsistencyPacketUp

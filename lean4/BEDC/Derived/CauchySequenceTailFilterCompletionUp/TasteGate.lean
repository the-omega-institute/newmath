import BEDC.Derived.CauchySequenceTailFilterCompletionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceTailFilterCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchySequenceTailFilterCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceTailFilterCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceTailFilterCompletionEncodeBHist h

def cauchySequenceTailFilterCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceTailFilterCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceTailFilterCompletionDecodeBHist tail)

private theorem cauchySequenceTailFilterCompletionDecodeEncode :
    ∀ h : BHist,
      cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceTailFilterCompletionFields :
    CauchySequenceTailFilterCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceTailFilterCompletionUp.mk T F C D W R E H K P N =>
      [T, F, C, D, W, R, E, H, K, P, N]

def cauchySequenceTailFilterCompletionToEventFlow :
    CauchySequenceTailFilterCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchySequenceTailFilterCompletionFields x).map
      cauchySequenceTailFilterCompletionEncodeBHist

private def cauchySequenceTailFilterCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceTailFilterCompletionEventAt index rest

def cauchySequenceTailFilterCompletionFromEventFlow
    (flow : EventFlow) : Option CauchySequenceTailFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySequenceTailFilterCompletionUp.mk
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 0 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 1 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 2 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 3 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 4 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 5 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 6 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 7 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 8 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 9 flow))
      (cauchySequenceTailFilterCompletionDecodeBHist
        (cauchySequenceTailFilterCompletionEventAt 10 flow)))

private theorem cauchySequenceTailFilterCompletionRoundTrip
    (x : CauchySequenceTailFilterCompletionUp) :
    cauchySequenceTailFilterCompletionFromEventFlow
      (cauchySequenceTailFilterCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F C D W R E H K P N =>
      change
        some
          (CauchySequenceTailFilterCompletionUp.mk
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist T))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist F))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist C))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist D))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist W))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist R))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist E))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist H))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist K))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist P))
            (cauchySequenceTailFilterCompletionDecodeBHist
              (cauchySequenceTailFilterCompletionEncodeBHist N))) =
          some (CauchySequenceTailFilterCompletionUp.mk T F C D W R E H K P N)
      rw [cauchySequenceTailFilterCompletionDecodeEncode T,
        cauchySequenceTailFilterCompletionDecodeEncode F,
        cauchySequenceTailFilterCompletionDecodeEncode C,
        cauchySequenceTailFilterCompletionDecodeEncode D,
        cauchySequenceTailFilterCompletionDecodeEncode W,
        cauchySequenceTailFilterCompletionDecodeEncode R,
        cauchySequenceTailFilterCompletionDecodeEncode E,
        cauchySequenceTailFilterCompletionDecodeEncode H,
        cauchySequenceTailFilterCompletionDecodeEncode K,
        cauchySequenceTailFilterCompletionDecodeEncode P,
        cauchySequenceTailFilterCompletionDecodeEncode N]

private theorem cauchySequenceTailFilterCompletionToEventFlow_injective
    {x y : CauchySequenceTailFilterCompletionUp} :
    cauchySequenceTailFilterCompletionToEventFlow x =
        cauchySequenceTailFilterCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceTailFilterCompletionFromEventFlow
          (cauchySequenceTailFilterCompletionToEventFlow x) =
        cauchySequenceTailFilterCompletionFromEventFlow
          (cauchySequenceTailFilterCompletionToEventFlow y) :=
    congrArg cauchySequenceTailFilterCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceTailFilterCompletionRoundTrip x).symm
      (Eq.trans hread (cauchySequenceTailFilterCompletionRoundTrip y)))

instance cauchySequenceTailFilterCompletionBHistCarrier :
    BHistCarrier CauchySequenceTailFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceTailFilterCompletionToEventFlow
  fromEventFlow := cauchySequenceTailFilterCompletionFromEventFlow

instance cauchySequenceTailFilterCompletionChapterTasteGate :
    ChapterTasteGate CauchySequenceTailFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceTailFilterCompletionFromEventFlow
        (cauchySequenceTailFilterCompletionToEventFlow x) = some x
    exact cauchySequenceTailFilterCompletionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceTailFilterCompletionToEventFlow_injective heq)

theorem CauchySequenceTailFilterCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchySequenceTailFilterCompletionUp) ∧
      Nonempty (ChapterTasteGate CauchySequenceTailFilterCompletionUp) ∧
        (∀ x : CauchySequenceTailFilterCompletionUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∃ x : CauchySequenceTailFilterCompletionUp,
            List.Mem ([] : RawEvent) (BHistCarrier.toEventFlow x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  refine
    ⟨⟨cauchySequenceTailFilterCompletionBHistCarrier⟩,
      ⟨cauchySequenceTailFilterCompletionChapterTasteGate⟩, ?_, ?_⟩
  · intro x
    change
      cauchySequenceTailFilterCompletionFromEventFlow
        (cauchySequenceTailFilterCompletionToEventFlow x) = some x
    exact cauchySequenceTailFilterCompletionRoundTrip x
  · exact
      ⟨CauchySequenceTailFilterCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty, by
          simp only [BHistCarrier.toEventFlow, cauchySequenceTailFilterCompletionToEventFlow,
            cauchySequenceTailFilterCompletionFields]
          exact List.Mem.head _⟩

end BEDC.Derived.CauchySequenceTailFilterCompletionUp

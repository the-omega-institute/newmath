import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotContinuedFractionBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotContinuedFractionBridgeUp : Type where
  | mk
      (tree approximation farey continuedFraction convergent interval window readback realSeal
        transport continuation provenance name : BHist) :
      SternBrocotContinuedFractionBridgeUp

private def sternBrocotContinuedFractionBridgeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotContinuedFractionBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotContinuedFractionBridgeEncodeBHist h

private def sternBrocotContinuedFractionBridgeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotContinuedFractionBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotContinuedFractionBridgeDecodeBHist tail)

private theorem sternBrocotContinuedFractionBridge_decode_encode_bhist :
    ∀ h : BHist,
      sternBrocotContinuedFractionBridgeDecodeBHist
        (sternBrocotContinuedFractionBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def sternBrocotContinuedFractionBridgeToEventFlow :
    SternBrocotContinuedFractionBridgeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotContinuedFractionBridgeUp.mk tree approximation farey continuedFraction
      convergent interval window readback realSeal transport continuation provenance name =>
      [[BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist tree,
        [BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist approximation,
        [BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist farey,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist continuedFraction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist convergent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist interval,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sternBrocotContinuedFractionBridgeEncodeBHist name]

private def sternBrocotContinuedFractionBridgeRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => sternBrocotContinuedFractionBridgeRawAt n rest

private def sternBrocotContinuedFractionBridgeLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => sternBrocotContinuedFractionBridgeLengthEq n rest

private def sternBrocotContinuedFractionBridgeFromEventFlow :
    EventFlow -> Option SternBrocotContinuedFractionBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match sternBrocotContinuedFractionBridgeLengthEq 26 flow with
      | true =>
          some
            (SternBrocotContinuedFractionBridgeUp.mk
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 1 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 3 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 5 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 7 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 9 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 11 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 13 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 15 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 17 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 19 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 21 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 23 flow))
              (sternBrocotContinuedFractionBridgeDecodeBHist
                (sternBrocotContinuedFractionBridgeRawAt 25 flow)))
      | false => none

private theorem sternBrocotContinuedFractionBridge_round_trip :
    ∀ x : SternBrocotContinuedFractionBridgeUp,
      sternBrocotContinuedFractionBridgeFromEventFlow
        (sternBrocotContinuedFractionBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tree approximation farey continuedFraction convergent interval window readback realSeal
      transport continuation provenance name =>
      change
        some
          (SternBrocotContinuedFractionBridgeUp.mk
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist tree))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist approximation))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist farey))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist continuedFraction))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist convergent))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist interval))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist window))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist readback))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist realSeal))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist transport))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist continuation))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist provenance))
            (sternBrocotContinuedFractionBridgeDecodeBHist
              (sternBrocotContinuedFractionBridgeEncodeBHist name))) =
        some
          (SternBrocotContinuedFractionBridgeUp.mk tree approximation farey
            continuedFraction convergent interval window readback realSeal transport continuation
            provenance name)
      rw [sternBrocotContinuedFractionBridge_decode_encode_bhist tree,
        sternBrocotContinuedFractionBridge_decode_encode_bhist approximation,
        sternBrocotContinuedFractionBridge_decode_encode_bhist farey,
        sternBrocotContinuedFractionBridge_decode_encode_bhist continuedFraction,
        sternBrocotContinuedFractionBridge_decode_encode_bhist convergent,
        sternBrocotContinuedFractionBridge_decode_encode_bhist interval,
        sternBrocotContinuedFractionBridge_decode_encode_bhist window,
        sternBrocotContinuedFractionBridge_decode_encode_bhist readback,
        sternBrocotContinuedFractionBridge_decode_encode_bhist realSeal,
        sternBrocotContinuedFractionBridge_decode_encode_bhist transport,
        sternBrocotContinuedFractionBridge_decode_encode_bhist continuation,
        sternBrocotContinuedFractionBridge_decode_encode_bhist provenance,
        sternBrocotContinuedFractionBridge_decode_encode_bhist name]

private theorem sternBrocotContinuedFractionBridgeToEventFlow_injective
    {x y : SternBrocotContinuedFractionBridgeUp} :
    sternBrocotContinuedFractionBridgeToEventFlow x =
      sternBrocotContinuedFractionBridgeToEventFlow y ->
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow x) =
        sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow y) :=
    congrArg sternBrocotContinuedFractionBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sternBrocotContinuedFractionBridge_round_trip x).symm
      (Eq.trans hread (sternBrocotContinuedFractionBridge_round_trip y)))

instance sternBrocotContinuedFractionBridgeBHistCarrier :
    BHistCarrier SternBrocotContinuedFractionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotContinuedFractionBridgeToEventFlow
  fromEventFlow := sternBrocotContinuedFractionBridgeFromEventFlow

instance sternBrocotContinuedFractionBridgeChapterTasteGate :
    ChapterTasteGate SternBrocotContinuedFractionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sternBrocotContinuedFractionBridgeFromEventFlow
        (sternBrocotContinuedFractionBridgeToEventFlow x) = some x
    exact sternBrocotContinuedFractionBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sternBrocotContinuedFractionBridgeToEventFlow_injective heq)

theorem SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sternBrocotContinuedFractionBridgeDecodeBHist
        (sternBrocotContinuedFractionBridgeEncodeBHist h) = h) ∧
      (∀ x : SternBrocotContinuedFractionBridgeUp,
        sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow x) = some x) ∧
        (∀ x y : SternBrocotContinuedFractionBridgeUp,
          sternBrocotContinuedFractionBridgeToEventFlow x =
            sternBrocotContinuedFractionBridgeToEventFlow y ->
          x = y) ∧
          sternBrocotContinuedFractionBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨sternBrocotContinuedFractionBridge_decode_encode_bhist,
      sternBrocotContinuedFractionBridge_round_trip,
      by
        intro x y heq
        exact sternBrocotContinuedFractionBridgeToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.SternBrocotContinuedFractionBridgeUp

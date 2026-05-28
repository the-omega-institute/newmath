import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StronglyExtensionalRealMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StronglyExtensionalRealMapUp : Type where
  | mk (X Y G A S R D H C P N : BHist) : StronglyExtensionalRealMapUp
  deriving DecidableEq

def stronglyExtensionalRealMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stronglyExtensionalRealMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stronglyExtensionalRealMapEncodeBHist h

def stronglyExtensionalRealMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stronglyExtensionalRealMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stronglyExtensionalRealMapDecodeBHist tail)

private theorem stronglyExtensionalRealMap_decode_encode_bhist :
    ∀ h : BHist,
      stronglyExtensionalRealMapDecodeBHist
        (stronglyExtensionalRealMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stronglyExtensionalRealMapToEventFlow :
    StronglyExtensionalRealMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StronglyExtensionalRealMapUp.mk X Y G A S R D H C P N =>
      [stronglyExtensionalRealMapEncodeBHist X,
        stronglyExtensionalRealMapEncodeBHist Y,
        stronglyExtensionalRealMapEncodeBHist G,
        stronglyExtensionalRealMapEncodeBHist A,
        stronglyExtensionalRealMapEncodeBHist S,
        stronglyExtensionalRealMapEncodeBHist R,
        stronglyExtensionalRealMapEncodeBHist D,
        stronglyExtensionalRealMapEncodeBHist H,
        stronglyExtensionalRealMapEncodeBHist C,
        stronglyExtensionalRealMapEncodeBHist P,
        stronglyExtensionalRealMapEncodeBHist N]

private def stronglyExtensionalRealMapRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => stronglyExtensionalRealMapRawAt n rest

private def stronglyExtensionalRealMapLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => stronglyExtensionalRealMapLengthEq n rest

def stronglyExtensionalRealMapFromEventFlow :
    EventFlow → Option StronglyExtensionalRealMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match stronglyExtensionalRealMapLengthEq 11 flow with
      | true =>
          some
            (StronglyExtensionalRealMapUp.mk
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 0 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 1 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 2 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 3 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 4 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 5 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 6 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 7 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 8 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 9 flow))
              (stronglyExtensionalRealMapDecodeBHist
                (stronglyExtensionalRealMapRawAt 10 flow)))
      | false => none

private theorem stronglyExtensionalRealMap_round_trip :
    ∀ x : StronglyExtensionalRealMapUp,
      stronglyExtensionalRealMapFromEventFlow
        (stronglyExtensionalRealMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G A S R D H C P N =>
      change
        some
          (StronglyExtensionalRealMapUp.mk
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist X))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist Y))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist G))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist A))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist S))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist R))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist D))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist H))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist C))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist P))
            (stronglyExtensionalRealMapDecodeBHist
              (stronglyExtensionalRealMapEncodeBHist N))) =
          some (StronglyExtensionalRealMapUp.mk X Y G A S R D H C P N)
      rw [stronglyExtensionalRealMap_decode_encode_bhist X,
        stronglyExtensionalRealMap_decode_encode_bhist Y,
        stronglyExtensionalRealMap_decode_encode_bhist G,
        stronglyExtensionalRealMap_decode_encode_bhist A,
        stronglyExtensionalRealMap_decode_encode_bhist S,
        stronglyExtensionalRealMap_decode_encode_bhist R,
        stronglyExtensionalRealMap_decode_encode_bhist D,
        stronglyExtensionalRealMap_decode_encode_bhist H,
        stronglyExtensionalRealMap_decode_encode_bhist C,
        stronglyExtensionalRealMap_decode_encode_bhist P,
        stronglyExtensionalRealMap_decode_encode_bhist N]

private theorem stronglyExtensionalRealMapToEventFlow_injective
    {x y : StronglyExtensionalRealMapUp} :
    stronglyExtensionalRealMapToEventFlow x =
        stronglyExtensionalRealMapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stronglyExtensionalRealMapFromEventFlow
          (stronglyExtensionalRealMapToEventFlow x) =
        stronglyExtensionalRealMapFromEventFlow
          (stronglyExtensionalRealMapToEventFlow y) :=
    congrArg stronglyExtensionalRealMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stronglyExtensionalRealMap_round_trip x).symm
      (Eq.trans hread (stronglyExtensionalRealMap_round_trip y)))

instance stronglyExtensionalRealMapBHistCarrier :
    BHistCarrier StronglyExtensionalRealMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stronglyExtensionalRealMapToEventFlow
  fromEventFlow := stronglyExtensionalRealMapFromEventFlow

instance stronglyExtensionalRealMapChapterTasteGate :
    ChapterTasteGate StronglyExtensionalRealMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stronglyExtensionalRealMapFromEventFlow
        (stronglyExtensionalRealMapToEventFlow x) = some x
    exact stronglyExtensionalRealMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stronglyExtensionalRealMapToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StronglyExtensionalRealMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stronglyExtensionalRealMapChapterTasteGate

theorem StronglyExtensionalRealMapTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stronglyExtensionalRealMapDecodeBHist
        (stronglyExtensionalRealMapEncodeBHist h) = h) ∧
      (∀ x : StronglyExtensionalRealMapUp,
        stronglyExtensionalRealMapFromEventFlow
          (stronglyExtensionalRealMapToEventFlow x) = some x) ∧
        (∀ x y : StronglyExtensionalRealMapUp,
          stronglyExtensionalRealMapToEventFlow x =
            stronglyExtensionalRealMapToEventFlow y → x = y) ∧
          stronglyExtensionalRealMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨stronglyExtensionalRealMap_decode_encode_bhist,
      stronglyExtensionalRealMap_round_trip,
      by
        intro x y heq
        exact stronglyExtensionalRealMapToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.StronglyExtensionalRealMapUp

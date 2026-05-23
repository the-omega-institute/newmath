import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamMapUp : Type where
  | mk (S T F W Q D R H C P N : BHist) : StreamMapUp
  deriving DecidableEq

def streamMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamMapEncodeBHist h

def streamMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamMapDecodeBHist tail)

private theorem streamMap_decode_encode_bhist :
    ∀ h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def streamMapFields : StreamMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamMapUp.mk S T F W Q D R H C P N => [S, T, F, W, Q, D, R, H, C, P, N]

def streamMapToEventFlow : StreamMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map streamMapEncodeBHist (streamMapFields x)

def streamMapEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => streamMapEventAt index rest

def streamMapFromEventFlow : EventFlow → Option StreamMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (StreamMapUp.mk
          (streamMapDecodeBHist (streamMapEventAt 0 flow))
          (streamMapDecodeBHist (streamMapEventAt 1 flow))
          (streamMapDecodeBHist (streamMapEventAt 2 flow))
          (streamMapDecodeBHist (streamMapEventAt 3 flow))
          (streamMapDecodeBHist (streamMapEventAt 4 flow))
          (streamMapDecodeBHist (streamMapEventAt 5 flow))
          (streamMapDecodeBHist (streamMapEventAt 6 flow))
          (streamMapDecodeBHist (streamMapEventAt 7 flow))
          (streamMapDecodeBHist (streamMapEventAt 8 flow))
          (streamMapDecodeBHist (streamMapEventAt 9 flow))
          (streamMapDecodeBHist (streamMapEventAt 10 flow)))

private theorem streamMap_round_trip :
    ∀ x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T F W Q D R H C P N =>
      change
        some
          (StreamMapUp.mk
            (streamMapDecodeBHist (streamMapEncodeBHist S))
            (streamMapDecodeBHist (streamMapEncodeBHist T))
            (streamMapDecodeBHist (streamMapEncodeBHist F))
            (streamMapDecodeBHist (streamMapEncodeBHist W))
            (streamMapDecodeBHist (streamMapEncodeBHist Q))
            (streamMapDecodeBHist (streamMapEncodeBHist D))
            (streamMapDecodeBHist (streamMapEncodeBHist R))
            (streamMapDecodeBHist (streamMapEncodeBHist H))
            (streamMapDecodeBHist (streamMapEncodeBHist C))
            (streamMapDecodeBHist (streamMapEncodeBHist P))
            (streamMapDecodeBHist (streamMapEncodeBHist N))) =
          some (StreamMapUp.mk S T F W Q D R H C P N)
      rw [streamMap_decode_encode_bhist S,
        streamMap_decode_encode_bhist T,
        streamMap_decode_encode_bhist F,
        streamMap_decode_encode_bhist W,
        streamMap_decode_encode_bhist Q,
        streamMap_decode_encode_bhist D,
        streamMap_decode_encode_bhist R,
        streamMap_decode_encode_bhist H,
        streamMap_decode_encode_bhist C,
        streamMap_decode_encode_bhist P,
        streamMap_decode_encode_bhist N]

private theorem streamMapToEventFlow_injective {x y : StreamMapUp} :
    streamMapToEventFlow x = streamMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamMapFromEventFlow (streamMapToEventFlow x) =
        streamMapFromEventFlow (streamMapToEventFlow y) :=
    congrArg streamMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (streamMap_round_trip x).symm
      (Eq.trans hread (streamMap_round_trip y)))

private theorem streamMap_field_faithful :
    ∀ x y : StreamMapUp, streamMapFields x = streamMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ T₁ F₁ W₁ Q₁ D₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ F₂ W₂ Q₂ D₂ R₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance streamMapBHistCarrier : BHistCarrier StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamMapToEventFlow
  fromEventFlow := streamMapFromEventFlow

instance streamMapChapterTasteGate : ChapterTasteGate StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamMapFromEventFlow (streamMapToEventFlow x) = some x
    exact streamMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (streamMapToEventFlow_injective heq)

instance streamMapFieldFaithful : FieldFaithful StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamMapFields
  field_faithful := streamMap_field_faithful

instance streamMapNontrivial : Nontrivial StreamMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StreamMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  streamMapChapterTasteGate

theorem StreamMapUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, streamMapDecodeBHist (streamMapEncodeBHist h) = h) ∧
      (∀ x : StreamMapUp, streamMapFromEventFlow (streamMapToEventFlow x) = some x) ∧
        (∀ x y : StreamMapUp, streamMapToEventFlow x = streamMapToEventFlow y → x = y) ∧
          (∀ x y : StreamMapUp, streamMapFields x = streamMapFields y → x = y) ∧
            streamMapEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨streamMap_decode_encode_bhist,
      streamMap_round_trip,
      (fun _ _ heq => streamMapToEventFlow_injective heq),
      streamMap_field_faithful,
      rfl⟩

end BEDC.Derived.StreamMapUp

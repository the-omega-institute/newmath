import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TightRealIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TightRealIntervalUp : Type where
  | mk :
      (lowerEndpoint upperEndpoint rationalCell dyadicRefinement streamWindow
        regularReadback realSeal transport replay provenance name : BHist) →
      TightRealIntervalUp
  deriving DecidableEq

def tightRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tightRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tightRealIntervalEncodeBHist h

def tightRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tightRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tightRealIntervalDecodeBHist tail)

private theorem tightRealInterval_decode_encode_bhist :
    ∀ h : BHist, tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tightRealIntervalFields : TightRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TightRealIntervalUp.mk lowerEndpoint upperEndpoint rationalCell dyadicRefinement
      streamWindow regularReadback realSeal transport replay provenance name =>
      [lowerEndpoint, upperEndpoint, rationalCell, dyadicRefinement, streamWindow,
        regularReadback, realSeal, transport, replay, provenance, name]

def tightRealIntervalToEventFlow : TightRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tightRealIntervalFields x).map tightRealIntervalEncodeBHist

private def tightRealIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tightRealIntervalEventAt index rest

def tightRealIntervalFromEventFlow : EventFlow → Option TightRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TightRealIntervalUp.mk
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 0 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 1 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 2 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 3 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 4 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 5 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 6 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 7 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 8 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 9 ef))
        (tightRealIntervalDecodeBHist (tightRealIntervalEventAt 10 ef)))

private theorem tightRealInterval_round_trip :
    ∀ x : TightRealIntervalUp,
      tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lowerEndpoint upperEndpoint rationalCell dyadicRefinement streamWindow regularReadback
      realSeal transport replay provenance name =>
      change
        some
          (TightRealIntervalUp.mk
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist lowerEndpoint))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist upperEndpoint))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist rationalCell))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist dyadicRefinement))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist streamWindow))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist regularReadback))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist realSeal))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist transport))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist replay))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist provenance))
            (tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist name))) =
          some
            (TightRealIntervalUp.mk lowerEndpoint upperEndpoint rationalCell dyadicRefinement
              streamWindow regularReadback realSeal transport replay provenance name)
      rw [tightRealInterval_decode_encode_bhist lowerEndpoint,
        tightRealInterval_decode_encode_bhist upperEndpoint,
        tightRealInterval_decode_encode_bhist rationalCell,
        tightRealInterval_decode_encode_bhist dyadicRefinement,
        tightRealInterval_decode_encode_bhist streamWindow,
        tightRealInterval_decode_encode_bhist regularReadback,
        tightRealInterval_decode_encode_bhist realSeal,
        tightRealInterval_decode_encode_bhist transport,
        tightRealInterval_decode_encode_bhist replay,
        tightRealInterval_decode_encode_bhist provenance,
        tightRealInterval_decode_encode_bhist name]

private theorem tightRealIntervalToEventFlow_injective {x y : TightRealIntervalUp} :
    tightRealIntervalToEventFlow x = tightRealIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) =
        tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow y) :=
    congrArg tightRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tightRealInterval_round_trip x).symm
      (Eq.trans hread (tightRealInterval_round_trip y)))

instance tightRealIntervalBHistCarrier : BHistCarrier TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tightRealIntervalToEventFlow
  fromEventFlow := tightRealIntervalFromEventFlow

instance tightRealIntervalChapterTasteGate : ChapterTasteGate TightRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tightRealIntervalFromEventFlow (tightRealIntervalToEventFlow x) = some x
    exact tightRealInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tightRealIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TightRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tightRealIntervalChapterTasteGate

namespace TasteGate

theorem TightRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, tightRealIntervalDecodeBHist (tightRealIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier TightRealIntervalUp) ∧
        Nonempty (ChapterTasteGate TightRealIntervalUp) ∧
          tightRealIntervalFields
              (TightRealIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨tightRealInterval_decode_encode_bhist, ⟨tightRealIntervalBHistCarrier⟩,
      ⟨tightRealIntervalChapterTasteGate⟩, rfl⟩

end TasteGate

end BEDC.Derived.TightRealIntervalUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealComparisonModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealComparisonModulusUp : Type where
  | mk (Q A D B R E H C P N : BHist) : LocatedRealComparisonModulusUp
  deriving DecidableEq

def locatedRealComparisonModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealComparisonModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealComparisonModulusEncodeBHist h

def locatedRealComparisonModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealComparisonModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealComparisonModulusDecodeBHist tail)

private theorem locatedRealComparisonModulus_decode_encode_bhist :
    forall h : BHist,
      locatedRealComparisonModulusDecodeBHist
          (locatedRealComparisonModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealComparisonModulusFields :
    LocatedRealComparisonModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealComparisonModulusUp.mk Q A D B R E H C P N => [Q, A, D, B, R, E, H, C, P, N]

def locatedRealComparisonModulusToEventFlow :
    LocatedRealComparisonModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealComparisonModulusFields x).map locatedRealComparisonModulusEncodeBHist

private def locatedRealComparisonModulusEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealComparisonModulusEventAt index rest

def locatedRealComparisonModulusFromEventFlow
    (ef : EventFlow) : Option LocatedRealComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealComparisonModulusUp.mk
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 0 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 1 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 2 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 3 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 4 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 5 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 6 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 7 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 8 ef))
      (locatedRealComparisonModulusDecodeBHist
        (locatedRealComparisonModulusEventAt 9 ef)))

private theorem locatedRealComparisonModulus_round_trip
    (x : LocatedRealComparisonModulusUp) :
    locatedRealComparisonModulusFromEventFlow
        (locatedRealComparisonModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q A D B R E H C P N =>
      change
        some
          (LocatedRealComparisonModulusUp.mk
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist Q))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist A))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist D))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist B))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist R))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist E))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist H))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist C))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist P))
            (locatedRealComparisonModulusDecodeBHist
              (locatedRealComparisonModulusEncodeBHist N))) =
          some (LocatedRealComparisonModulusUp.mk Q A D B R E H C P N)
      rw [locatedRealComparisonModulus_decode_encode_bhist Q,
        locatedRealComparisonModulus_decode_encode_bhist A,
        locatedRealComparisonModulus_decode_encode_bhist D,
        locatedRealComparisonModulus_decode_encode_bhist B,
        locatedRealComparisonModulus_decode_encode_bhist R,
        locatedRealComparisonModulus_decode_encode_bhist E,
        locatedRealComparisonModulus_decode_encode_bhist H,
        locatedRealComparisonModulus_decode_encode_bhist C,
        locatedRealComparisonModulus_decode_encode_bhist P,
        locatedRealComparisonModulus_decode_encode_bhist N]

private theorem locatedRealComparisonModulusToEventFlow_injective
    {x y : LocatedRealComparisonModulusUp} :
    locatedRealComparisonModulusToEventFlow x =
      locatedRealComparisonModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealComparisonModulusFromEventFlow
          (locatedRealComparisonModulusToEventFlow x) =
        locatedRealComparisonModulusFromEventFlow
          (locatedRealComparisonModulusToEventFlow y) :=
    congrArg locatedRealComparisonModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealComparisonModulus_round_trip x).symm
      (Eq.trans hread (locatedRealComparisonModulus_round_trip y)))

instance locatedRealComparisonModulusBHistCarrier :
    BHistCarrier LocatedRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealComparisonModulusToEventFlow
  fromEventFlow := locatedRealComparisonModulusFromEventFlow

instance locatedRealComparisonModulusChapterTasteGate :
    ChapterTasteGate LocatedRealComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealComparisonModulusFromEventFlow
          (locatedRealComparisonModulusToEventFlow x) =
        some x
    exact locatedRealComparisonModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealComparisonModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealComparisonModulusChapterTasteGate

theorem LocatedRealComparisonModulusTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedRealComparisonModulusDecodeBHist
          (locatedRealComparisonModulusEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier LocatedRealComparisonModulusUp) ∧
        Nonempty (ChapterTasteGate LocatedRealComparisonModulusUp) ∧
          locatedRealComparisonModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact locatedRealComparisonModulus_decode_encode_bhist
  · constructor
    · exact ⟨locatedRealComparisonModulusBHistCarrier⟩
    · constructor
      · exact ⟨locatedRealComparisonModulusChapterTasteGate⟩
      · rfl

end BEDC.Derived.LocatedRealComparisonModulusUp

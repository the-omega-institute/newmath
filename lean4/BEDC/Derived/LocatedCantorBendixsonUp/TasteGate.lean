import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCantorBendixsonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCantorBendixsonUp : Type where
  | mk (K C D I P R H Q S N : BHist) : LocatedCantorBendixsonUp
  deriving DecidableEq

def locatedCantorBendixsonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCantorBendixsonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCantorBendixsonEncodeBHist h

def locatedCantorBendixsonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCantorBendixsonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCantorBendixsonDecodeBHist tail)

private theorem locatedCantorBendixson_decode_encode_bhist :
    ∀ h : BHist,
      locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCantorBendixsonFields : LocatedCantorBendixsonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCantorBendixsonUp.mk K C D I P R H Q S N => [K, C, D, I, P, R, H, Q, S, N]

def locatedCantorBendixsonToEventFlow : LocatedCantorBendixsonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCantorBendixsonFields x).map locatedCantorBendixsonEncodeBHist

private def locatedCantorBendixsonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCantorBendixsonEventAtDefault index rest

def locatedCantorBendixsonFromEventFlow (ef : EventFlow) :
    Option LocatedCantorBendixsonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCantorBendixsonUp.mk
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 0 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 1 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 2 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 3 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 4 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 5 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 6 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 7 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 8 ef))
      (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEventAtDefault 9 ef)))

private theorem locatedCantorBendixson_round_trip (x : LocatedCantorBendixsonUp) :
    locatedCantorBendixsonFromEventFlow
      (locatedCantorBendixsonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K C D I P R H Q S N =>
      change
        some
          (LocatedCantorBendixsonUp.mk
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist K))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist C))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist D))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist I))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist P))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist R))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist H))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist Q))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist S))
            (locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist N))) =
          some (LocatedCantorBendixsonUp.mk K C D I P R H Q S N)
      rw [locatedCantorBendixson_decode_encode_bhist K,
        locatedCantorBendixson_decode_encode_bhist C,
        locatedCantorBendixson_decode_encode_bhist D,
        locatedCantorBendixson_decode_encode_bhist I,
        locatedCantorBendixson_decode_encode_bhist P,
        locatedCantorBendixson_decode_encode_bhist R,
        locatedCantorBendixson_decode_encode_bhist H,
        locatedCantorBendixson_decode_encode_bhist Q,
        locatedCantorBendixson_decode_encode_bhist S,
        locatedCantorBendixson_decode_encode_bhist N]

private theorem locatedCantorBendixsonToEventFlow_injective
    {x y : LocatedCantorBendixsonUp} :
    locatedCantorBendixsonToEventFlow x =
      locatedCantorBendixsonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCantorBendixsonFromEventFlow (locatedCantorBendixsonToEventFlow x) =
        locatedCantorBendixsonFromEventFlow (locatedCantorBendixsonToEventFlow y) :=
    congrArg locatedCantorBendixsonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCantorBendixson_round_trip x).symm
      (Eq.trans hread (locatedCantorBendixson_round_trip y)))

instance locatedCantorBendixsonBHistCarrier :
    BHistCarrier LocatedCantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCantorBendixsonToEventFlow
  fromEventFlow := locatedCantorBendixsonFromEventFlow

instance locatedCantorBendixsonChapterTasteGate :
    ChapterTasteGate LocatedCantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCantorBendixsonFromEventFlow
      (locatedCantorBendixsonToEventFlow x) = some x
    exact locatedCantorBendixson_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCantorBendixsonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCantorBendixsonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCantorBendixsonChapterTasteGate

theorem LocatedCantorBendixsonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        locatedCantorBendixsonDecodeBHist (locatedCantorBendixsonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCantorBendixsonUp) ∧
        Nonempty (ChapterTasteGate LocatedCantorBendixsonUp) ∧
          locatedCantorBendixsonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedCantorBendixson_decode_encode_bhist,
      ⟨locatedCantorBendixsonBHistCarrier⟩,
      ⟨locatedCantorBendixsonChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCantorBendixsonUp

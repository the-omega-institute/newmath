import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealUp : Type where
  | mk (S R D E Q H C P N : BHist) : LocatedRealUp
  deriving DecidableEq

def locatedRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealEncodeBHist h

def locatedRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealDecodeBHist tail)

private theorem locatedRealDecodeEncodeBHist :
    forall h : BHist, locatedRealDecodeBHist (locatedRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealFields : LocatedRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealUp.mk S R D E Q H C P N => [S, R, D, E, Q, H, C, P, N]

def locatedRealToEventFlow : LocatedRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealFields x).map locatedRealEncodeBHist

private def locatedRealEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealEventAtDefault index rest

def locatedRealFromEventFlow (ef : EventFlow) : Option LocatedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealUp.mk
      (locatedRealDecodeBHist (locatedRealEventAtDefault 0 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 1 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 2 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 3 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 4 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 5 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 6 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 7 ef))
      (locatedRealDecodeBHist (locatedRealEventAtDefault 8 ef)))

private theorem locatedReal_round_trip :
    forall x : LocatedRealUp,
      locatedRealFromEventFlow (locatedRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D E Q H C P N =>
      change
        some
          (LocatedRealUp.mk
            (locatedRealDecodeBHist (locatedRealEncodeBHist S))
            (locatedRealDecodeBHist (locatedRealEncodeBHist R))
            (locatedRealDecodeBHist (locatedRealEncodeBHist D))
            (locatedRealDecodeBHist (locatedRealEncodeBHist E))
            (locatedRealDecodeBHist (locatedRealEncodeBHist Q))
            (locatedRealDecodeBHist (locatedRealEncodeBHist H))
            (locatedRealDecodeBHist (locatedRealEncodeBHist C))
            (locatedRealDecodeBHist (locatedRealEncodeBHist P))
            (locatedRealDecodeBHist (locatedRealEncodeBHist N))) =
          some (LocatedRealUp.mk S R D E Q H C P N)
      rw [locatedRealDecodeEncodeBHist S,
        locatedRealDecodeEncodeBHist R,
        locatedRealDecodeEncodeBHist D,
        locatedRealDecodeEncodeBHist E,
        locatedRealDecodeEncodeBHist Q,
        locatedRealDecodeEncodeBHist H,
        locatedRealDecodeEncodeBHist C,
        locatedRealDecodeEncodeBHist P,
        locatedRealDecodeEncodeBHist N]

private theorem locatedRealToEventFlow_injective {x y : LocatedRealUp} :
    locatedRealToEventFlow x = locatedRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealFromEventFlow (locatedRealToEventFlow x) =
        locatedRealFromEventFlow (locatedRealToEventFlow y) :=
    congrArg locatedRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedReal_round_trip x).symm
      (Eq.trans hread (locatedReal_round_trip y)))

instance locatedRealBHistCarrier : BHistCarrier LocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealToEventFlow
  fromEventFlow := locatedRealFromEventFlow

instance locatedRealChapterTasteGate : ChapterTasteGate LocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealFromEventFlow (locatedRealToEventFlow x) = some x
    exact locatedReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealChapterTasteGate

theorem LocatedRealTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedRealUp) ∧ Nonempty (ChapterTasteGate LocatedRealUp) ∧
      (∀ x : LocatedRealUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro locatedRealBHistCarrier,
      Nonempty.intro locatedRealChapterTasteGate,
      locatedRealChapterTasteGate.round_trip⟩

end BEDC.Derived.LocatedRealUp

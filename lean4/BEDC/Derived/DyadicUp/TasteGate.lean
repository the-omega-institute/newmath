import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicUp : Type where
  | mk (Q S R E H C P N : BHist) : DyadicUp
  deriving DecidableEq

def dyadicEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicEncodeBHist h

def dyadicDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicDecodeBHist tail)

private theorem DyadicUpTasteGate_decode_encode :
    forall h : BHist, dyadicDecodeBHist (dyadicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicToEventFlow : DyadicUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicUp.mk Q S R E H C P N =>
      [[BMark.b0, BMark.b1, BMark.b0, BMark.b1],
        dyadicEncodeBHist Q,
        dyadicEncodeBHist S,
        dyadicEncodeBHist R,
        dyadicEncodeBHist E,
        dyadicEncodeBHist H,
        dyadicEncodeBHist C,
        dyadicEncodeBHist P,
        dyadicEncodeBHist N]

private def dyadicEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicEventAtDefault index rest

def dyadicFromEventFlow (ef : EventFlow) : Option DyadicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicUp.mk
      (dyadicDecodeBHist (dyadicEventAtDefault 1 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 2 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 3 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 4 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 5 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 6 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 7 ef))
      (dyadicDecodeBHist (dyadicEventAtDefault 8 ef)))

private theorem DyadicUpTasteGate_round_trip :
    forall x : DyadicUp, dyadicFromEventFlow (dyadicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S R E H C P N =>
      change
        some
          (DyadicUp.mk
            (dyadicDecodeBHist (dyadicEncodeBHist Q))
            (dyadicDecodeBHist (dyadicEncodeBHist S))
            (dyadicDecodeBHist (dyadicEncodeBHist R))
            (dyadicDecodeBHist (dyadicEncodeBHist E))
            (dyadicDecodeBHist (dyadicEncodeBHist H))
            (dyadicDecodeBHist (dyadicEncodeBHist C))
            (dyadicDecodeBHist (dyadicEncodeBHist P))
            (dyadicDecodeBHist (dyadicEncodeBHist N))) =
          some (DyadicUp.mk Q S R E H C P N)
      rw [DyadicUpTasteGate_decode_encode Q, DyadicUpTasteGate_decode_encode S,
        DyadicUpTasteGate_decode_encode R, DyadicUpTasteGate_decode_encode E,
        DyadicUpTasteGate_decode_encode H, DyadicUpTasteGate_decode_encode C,
        DyadicUpTasteGate_decode_encode P, DyadicUpTasteGate_decode_encode N]

private theorem DyadicUpTasteGate_toEventFlow_injective {x y : DyadicUp} :
    dyadicToEventFlow x = dyadicToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicFromEventFlow (dyadicToEventFlow x) =
        dyadicFromEventFlow (dyadicToEventFlow y) :=
    congrArg dyadicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicUpTasteGate_round_trip x).symm
      (Eq.trans hread (DyadicUpTasteGate_round_trip y)))

instance dyadicBHistCarrier : BHistCarrier DyadicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToEventFlow
  fromEventFlow := dyadicFromEventFlow

instance dyadicChapterTasteGate : ChapterTasteGate DyadicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicFromEventFlow (dyadicToEventFlow x) = some x
    exact DyadicUpTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicUpTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicChapterTasteGate

theorem DyadicUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicUp) ∧
      (forall h : BHist, dyadicDecodeBHist (dyadicEncodeBHist h) = h) ∧
        (forall x : DyadicUp, dyadicFromEventFlow (dyadicToEventFlow x) = some x) ∧
          (forall x y : DyadicUp, dyadicToEventFlow x = dyadicToEventFlow y -> x = y) ∧
            dyadicEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨dyadicChapterTasteGate⟩,
      DyadicUpTasteGate_decode_encode,
      DyadicUpTasteGate_round_trip,
      (fun _ _ heq => DyadicUpTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicUp

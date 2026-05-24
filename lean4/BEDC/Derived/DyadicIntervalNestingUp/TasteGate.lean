import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalNestingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalNestingUp : Type where
  | mk (D S R E I H C P N : BHist) : DyadicIntervalNestingUp
  deriving DecidableEq

def dyadicIntervalNestingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalNestingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalNestingEncodeBHist h

def dyadicIntervalNestingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalNestingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalNestingDecodeBHist tail)

private theorem dyadicIntervalNesting_decode_encode_bhist :
    ∀ h : BHist, dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalNestingFields : DyadicIntervalNestingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalNestingUp.mk D S R E I H C P N => [D, S, R, E, I, H, C, P, N]

def dyadicIntervalNestingToEventFlow : DyadicIntervalNestingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalNestingFields x).map dyadicIntervalNestingEncodeBHist

private def dyadicIntervalNestingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalNestingEventAt index rest

def dyadicIntervalNestingFromEventFlow : EventFlow → Option DyadicIntervalNestingUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DyadicIntervalNestingUp.mk
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 0 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 1 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 2 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 3 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 4 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 5 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 6 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 7 ef))
          (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEventAt 8 ef)))

private theorem dyadicIntervalNesting_round_trip :
    ∀ x : DyadicIntervalNestingUp,
      dyadicIntervalNestingFromEventFlow (dyadicIntervalNestingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E I H C P N =>
      change
        some
          (DyadicIntervalNestingUp.mk
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist D))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist S))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist R))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist E))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist I))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist H))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist C))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist P))
            (dyadicIntervalNestingDecodeBHist (dyadicIntervalNestingEncodeBHist N))) =
          some (DyadicIntervalNestingUp.mk D S R E I H C P N)
      rw [dyadicIntervalNesting_decode_encode_bhist D,
        dyadicIntervalNesting_decode_encode_bhist S,
        dyadicIntervalNesting_decode_encode_bhist R,
        dyadicIntervalNesting_decode_encode_bhist E,
        dyadicIntervalNesting_decode_encode_bhist I,
        dyadicIntervalNesting_decode_encode_bhist H,
        dyadicIntervalNesting_decode_encode_bhist C,
        dyadicIntervalNesting_decode_encode_bhist P,
        dyadicIntervalNesting_decode_encode_bhist N]

private theorem dyadicIntervalNestingToEventFlow_injective {x y : DyadicIntervalNestingUp} :
    dyadicIntervalNestingToEventFlow x = dyadicIntervalNestingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalNestingFromEventFlow (dyadicIntervalNestingToEventFlow x) =
        dyadicIntervalNestingFromEventFlow (dyadicIntervalNestingToEventFlow y) :=
    congrArg dyadicIntervalNestingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicIntervalNesting_round_trip x).symm
      (Eq.trans hread (dyadicIntervalNesting_round_trip y)))

instance dyadicIntervalNestingBHistCarrier : BHistCarrier DyadicIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalNestingToEventFlow
  fromEventFlow := dyadicIntervalNestingFromEventFlow

instance dyadicIntervalNestingChapterTasteGate :
    ChapterTasteGate DyadicIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalNestingFromEventFlow (dyadicIntervalNestingToEventFlow x) = some x
    exact dyadicIntervalNesting_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicIntervalNestingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicIntervalNestingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalNestingChapterTasteGate

end BEDC.Derived.DyadicIntervalNestingUp.TasteGate

namespace BEDC.Derived.DyadicIntervalNestingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem DyadicIntervalNestingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.dyadicIntervalNestingDecodeBHist
          (TasteGate.dyadicIntervalNestingEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.DyadicIntervalNestingUp,
        TasteGate.dyadicIntervalNestingFromEventFlow
            (TasteGate.dyadicIntervalNestingToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.DyadicIntervalNestingUp,
          TasteGate.dyadicIntervalNestingToEventFlow x =
              TasteGate.dyadicIntervalNestingToEventFlow y →
            x = y) ∧
          TasteGate.dyadicIntervalNestingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TasteGate.dyadicIntervalNesting_decode_encode_bhist,
      TasteGate.dyadicIntervalNesting_round_trip,
      (fun _ _ heq => TasteGate.dyadicIntervalNestingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalNestingUp

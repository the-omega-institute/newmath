import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicToleranceLadderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicToleranceLadderUp : Type where
  | mk (D S Q E T H C P N : BHist) : DyadicToleranceLadderUp
  deriving DecidableEq

def dyadicToleranceLadderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicToleranceLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicToleranceLadderEncodeBHist h

def dyadicToleranceLadderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicToleranceLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicToleranceLadderDecodeBHist tail)

private theorem DyadicToleranceLadderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, dyadicToleranceLadderDecodeBHist
      (dyadicToleranceLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicToleranceLadderFields : DyadicToleranceLadderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicToleranceLadderUp.mk D S Q E T H C P N => [D, S, Q, E, T, H, C, P, N]

def dyadicToleranceLadderToEventFlow : DyadicToleranceLadderUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicToleranceLadderFields x).map dyadicToleranceLadderEncodeBHist

private def dyadicToleranceLadderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicToleranceLadderEventAtDefault index rest

def dyadicToleranceLadderFromEventFlow
    (ef : EventFlow) : Option DyadicToleranceLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicToleranceLadderUp.mk
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 0 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 1 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 2 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 3 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 4 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 5 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 6 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 7 ef))
      (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEventAtDefault 8 ef)))

private theorem DyadicToleranceLadderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicToleranceLadderUp,
      dyadicToleranceLadderFromEventFlow
        (dyadicToleranceLadderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk D S Q E T H C P N =>
      change
        some
          (DyadicToleranceLadderUp.mk
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist D))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist S))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist Q))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist E))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist T))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist H))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist C))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist P))
            (dyadicToleranceLadderDecodeBHist (dyadicToleranceLadderEncodeBHist N))) =
          some (DyadicToleranceLadderUp.mk D S Q E T H C P N)
      rw [DyadicToleranceLadderTasteGate_single_carrier_alignment_decode D,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode S,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode Q,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode E,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode T,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode H,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode C,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode P,
        DyadicToleranceLadderTasteGate_single_carrier_alignment_decode N]

private theorem DyadicToleranceLadderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicToleranceLadderUp} :
    dyadicToleranceLadderToEventFlow x =
      dyadicToleranceLadderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicToleranceLadderFromEventFlow (dyadicToleranceLadderToEventFlow x) =
        dyadicToleranceLadderFromEventFlow (dyadicToleranceLadderToEventFlow y) :=
    congrArg dyadicToleranceLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicToleranceLadderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicToleranceLadderTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicToleranceLadderBHistCarrier :
    BHistCarrier DyadicToleranceLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicToleranceLadderToEventFlow
  fromEventFlow := dyadicToleranceLadderFromEventFlow

instance dyadicToleranceLadderChapterTasteGate :
    ChapterTasteGate DyadicToleranceLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicToleranceLadderFromEventFlow
        (dyadicToleranceLadderToEventFlow x) = some x
    exact DyadicToleranceLadderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicToleranceLadderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicToleranceLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicToleranceLadderChapterTasteGate

theorem DyadicToleranceLadderTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicToleranceLadderDecodeBHist
      (dyadicToleranceLadderEncodeBHist h) = h) ∧
      (∀ x : DyadicToleranceLadderUp,
        dyadicToleranceLadderFromEventFlow (dyadicToleranceLadderToEventFlow x) = some x) ∧
        (∀ x y : DyadicToleranceLadderUp,
          dyadicToleranceLadderToEventFlow x = dyadicToleranceLadderToEventFlow y → x = y) ∧
          dyadicToleranceLadderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DyadicToleranceLadderTasteGate_single_carrier_alignment_decode,
      DyadicToleranceLadderTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicToleranceLadderTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicToleranceLadderUp

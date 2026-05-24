import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySeparationUp : Type where
  | mk (L R W D M E H C P N : BHist) : RegularCauchySeparationUp
  deriving DecidableEq

def regularCauchySeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySeparationEncodeBHist h

def regularCauchySeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySeparationDecodeBHist tail)

private theorem RegularCauchySeparationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchySeparationDecodeBHist (regularCauchySeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySeparationToEventFlow : RegularCauchySeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySeparationUp.mk L R W D M E H C P N =>
      [regularCauchySeparationEncodeBHist L,
        regularCauchySeparationEncodeBHist R,
        regularCauchySeparationEncodeBHist W,
        regularCauchySeparationEncodeBHist D,
        regularCauchySeparationEncodeBHist M,
        regularCauchySeparationEncodeBHist E,
        regularCauchySeparationEncodeBHist H,
        regularCauchySeparationEncodeBHist C,
        regularCauchySeparationEncodeBHist P,
        regularCauchySeparationEncodeBHist N]

private def regularCauchySeparationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySeparationEventAtDefault index rest

def regularCauchySeparationFromEventFlow (ef : EventFlow) :
    Option RegularCauchySeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySeparationUp.mk
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 0 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 1 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 2 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 3 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 4 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 5 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 6 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 7 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 8 ef))
      (regularCauchySeparationDecodeBHist (regularCauchySeparationEventAtDefault 9 ef)))

private theorem RegularCauchySeparationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySeparationUp,
      regularCauchySeparationFromEventFlow (regularCauchySeparationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W D M E H C P N =>
      change
        some
            (RegularCauchySeparationUp.mk
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist L))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist R))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist W))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist D))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist M))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist E))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist H))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist C))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist P))
              (regularCauchySeparationDecodeBHist
                (regularCauchySeparationEncodeBHist N))) =
          some (RegularCauchySeparationUp.mk L R W D M E H C P N)
      rw [RegularCauchySeparationTasteGate_single_carrier_alignment_decode L,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode R,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode W,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode D,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode M,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode E,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode H,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode C,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode P,
        RegularCauchySeparationTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchySeparationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySeparationUp} :
    regularCauchySeparationToEventFlow x = regularCauchySeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySeparationFromEventFlow (regularCauchySeparationToEventFlow x) =
        regularCauchySeparationFromEventFlow (regularCauchySeparationToEventFlow y) :=
    congrArg regularCauchySeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySeparationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySeparationTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySeparationBHistCarrier : BHistCarrier RegularCauchySeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySeparationToEventFlow
  fromEventFlow := regularCauchySeparationFromEventFlow

instance regularCauchySeparationChapterTasteGate :
    ChapterTasteGate RegularCauchySeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySeparationFromEventFlow (regularCauchySeparationToEventFlow x) =
      some x
    exact RegularCauchySeparationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchySeparationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySeparationChapterTasteGate

theorem RegularCauchySeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchySeparationDecodeBHist (regularCauchySeparationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySeparationUp,
        regularCauchySeparationFromEventFlow (regularCauchySeparationToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchySeparationUp,
          regularCauchySeparationToEventFlow x = regularCauchySeparationToEventFlow y →
            x = y) ∧
          regularCauchySeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySeparationTasteGate_single_carrier_alignment_decode,
      RegularCauchySeparationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchySeparationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySeparationUp

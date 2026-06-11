import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDifferenceBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDifferenceBoundUp : Type where
  | mk (X Y W D E R H C P N : BHist) : RegularCauchyDifferenceBoundUp
  deriving DecidableEq

def regularCauchyDifferenceBoundFields :
    RegularCauchyDifferenceBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDifferenceBoundUp.mk X Y W D E R H C P N =>
      [X, Y, W, D, E, R, H, C, P, N]

def regularCauchyDifferenceBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDifferenceBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDifferenceBoundEncodeBHist h

def regularCauchyDifferenceBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDifferenceBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDifferenceBoundDecodeBHist tail)

private theorem RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyDifferenceBoundDecodeBHist
          (regularCauchyDifferenceBoundEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyDifferenceBoundToEventFlow :
    RegularCauchyDifferenceBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyDifferenceBoundEncodeBHist
        (regularCauchyDifferenceBoundFields x)

private def regularCauchyDifferenceBoundEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDifferenceBoundEventAt index rest

def regularCauchyDifferenceBoundFromEventFlow
    (ef : EventFlow) : Option RegularCauchyDifferenceBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDifferenceBoundUp.mk
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 0 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 1 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 2 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 3 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 4 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 5 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 6 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 7 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 8 ef))
      (regularCauchyDifferenceBoundDecodeBHist (regularCauchyDifferenceBoundEventAt 9 ef)))

private theorem RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyDifferenceBoundUp) :
    regularCauchyDifferenceBoundFromEventFlow
        (regularCauchyDifferenceBoundToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y W D E R H C P N =>
      change
        some
          (RegularCauchyDifferenceBoundUp.mk
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist X))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist Y))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist W))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist D))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist E))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist R))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist H))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist C))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist P))
            (regularCauchyDifferenceBoundDecodeBHist
              (regularCauchyDifferenceBoundEncodeBHist N))) =
          some (RegularCauchyDifferenceBoundUp.mk X Y W D E R H C P N)
      rw [RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode Y,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode N]

private theorem regularCauchyDifferenceBoundToEventFlow_injective
    {x y : RegularCauchyDifferenceBoundUp} :
    regularCauchyDifferenceBoundToEventFlow x =
        regularCauchyDifferenceBoundToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDifferenceBoundFromEventFlow
          (regularCauchyDifferenceBoundToEventFlow x) =
        regularCauchyDifferenceBoundFromEventFlow
          (regularCauchyDifferenceBoundToEventFlow y) :=
    congrArg regularCauchyDifferenceBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyDifferenceBoundBHistCarrier :
    BHistCarrier RegularCauchyDifferenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDifferenceBoundToEventFlow
  fromEventFlow := regularCauchyDifferenceBoundFromEventFlow

instance regularCauchyDifferenceBoundChapterTasteGate :
    ChapterTasteGate RegularCauchyDifferenceBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDifferenceBoundFromEventFlow
          (regularCauchyDifferenceBoundToEventFlow x) =
        some x
    exact RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDifferenceBoundToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyDifferenceBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDifferenceBoundChapterTasteGate

theorem RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyDifferenceBoundDecodeBHist
            (regularCauchyDifferenceBoundEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyDifferenceBoundUp,
        regularCauchyDifferenceBoundFromEventFlow
            (regularCauchyDifferenceBoundToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyDifferenceBoundUp,
          regularCauchyDifferenceBoundToEventFlow x =
              regularCauchyDifferenceBoundToEventFlow y →
            x = y) ∧
          regularCauchyDifferenceBoundEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyDifferenceBoundTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => regularCauchyDifferenceBoundToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyDifferenceBoundUp

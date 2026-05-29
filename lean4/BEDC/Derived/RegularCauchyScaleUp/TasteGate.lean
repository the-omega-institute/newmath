import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyScaleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyScaleUp : Type where
  | mk (Q A W DQ DA D E R H C P N : BHist) : RegularCauchyScaleUp

def regularCauchyScaleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyScaleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyScaleEncodeBHist h

def regularCauchyScaleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyScaleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyScaleDecodeBHist tail)

private theorem RegularCauchyScaleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyScaleFields : RegularCauchyScaleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyScaleUp.mk Q A W DQ DA D E R H C P N => [Q, A, W, DQ, DA, D, E, R, H, C, P, N]

def regularCauchyScaleToEventFlow : RegularCauchyScaleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyScaleFields x).map regularCauchyScaleEncodeBHist

private def regularCauchyScaleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyScaleEventAtDefault index rest

def regularCauchyScaleFromEventFlow :
    EventFlow → Option RegularCauchyScaleUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyScaleUp.mk
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 0 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 1 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 2 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 3 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 4 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 5 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 6 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 7 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 8 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 9 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 10 ef))
          (regularCauchyScaleDecodeBHist (regularCauchyScaleEventAtDefault 11 ef)))

private theorem RegularCauchyScaleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyScaleUp,
      regularCauchyScaleFromEventFlow (regularCauchyScaleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A W DQ DA D E R H C P N =>
      change
        some
          (RegularCauchyScaleUp.mk
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist Q))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist A))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist W))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist DQ))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist DA))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist D))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist E))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist R))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist H))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist C))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist P))
            (regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist N))) =
          some (RegularCauchyScaleUp.mk Q A W DQ DA D E R H C P N)
      rw [RegularCauchyScaleTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode A,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode W,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode DQ,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode DA,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode D,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode E,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode R,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode H,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode C,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode P,
        RegularCauchyScaleTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyScaleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyScaleUp} :
    regularCauchyScaleToEventFlow x = regularCauchyScaleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyScaleFromEventFlow (regularCauchyScaleToEventFlow x) =
        regularCauchyScaleFromEventFlow (regularCauchyScaleToEventFlow y) :=
    congrArg regularCauchyScaleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyScaleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyScaleTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyScaleBHistCarrier :
    BHistCarrier RegularCauchyScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyScaleToEventFlow
  fromEventFlow := regularCauchyScaleFromEventFlow

instance regularCauchyScaleChapterTasteGate :
    ChapterTasteGate RegularCauchyScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyScaleFromEventFlow (regularCauchyScaleToEventFlow x) = some x
    exact RegularCauchyScaleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyScaleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyScaleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyScaleChapterTasteGate

theorem RegularCauchyScaleTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyScaleDecodeBHist (regularCauchyScaleEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyScaleUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyScaleUp) ∧
          regularCauchyScaleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨RegularCauchyScaleTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyScaleBHistCarrier⟩,
      ⟨regularCauchyScaleChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyScaleUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompleteOrderedFieldUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompleteOrderedFieldUniquenessUp : Type where
  | mk : (K0 K1 R0 R1 Q0 Q1 D A0 A1 F0 F1 G H C P N : BHist) →
      CauchyCompleteOrderedFieldUniquenessUp
  deriving DecidableEq

def cauchyCompleteOrderedFieldUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompleteOrderedFieldUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompleteOrderedFieldUniquenessEncodeBHist h

def cauchyCompleteOrderedFieldUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (cauchyCompleteOrderedFieldUniquenessDecodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (cauchyCompleteOrderedFieldUniquenessDecodeBHist tail)

private theorem cauchyCompleteOrderedFieldUniquenessDecode_encode :
    ∀ h : BHist,
      cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompleteOrderedFieldUniquenessFields :
    CauchyCompleteOrderedFieldUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompleteOrderedFieldUniquenessUp.mk
      K0 K1 R0 R1 Q0 Q1 D A0 A1 F0 F1 G H C P N =>
      [K0, K1, R0, R1, Q0, Q1, D, A0, A1, F0, F1, G, H, C, P, N]

def cauchyCompleteOrderedFieldUniquenessToEventFlow :
    CauchyCompleteOrderedFieldUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompleteOrderedFieldUniquenessFields x).map
      cauchyCompleteOrderedFieldUniquenessEncodeBHist

private def cauchyCompleteOrderedFieldUniquenessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompleteOrderedFieldUniquenessEventAtDefault index rest

def cauchyCompleteOrderedFieldUniquenessFromEventFlow
    (ef : EventFlow) : Option CauchyCompleteOrderedFieldUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompleteOrderedFieldUniquenessUp.mk
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 0 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 1 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 2 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 3 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 4 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 5 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 6 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 7 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 8 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 9 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 10 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 11 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 12 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 13 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 14 ef))
      (cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEventAtDefault 15 ef)))

private theorem cauchyCompleteOrderedFieldUniqueness_round_trip :
    ∀ x : CauchyCompleteOrderedFieldUniquenessUp,
      cauchyCompleteOrderedFieldUniquenessFromEventFlow
        (cauchyCompleteOrderedFieldUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K0 K1 R0 R1 Q0 Q1 D A0 A1 F0 F1 G H C P N =>
      change
        some
          (CauchyCompleteOrderedFieldUniquenessUp.mk
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist K0))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist K1))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist R0))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist R1))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist Q0))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist Q1))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist D))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist A0))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist A1))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist F0))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist F1))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist G))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist H))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist C))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist P))
            (cauchyCompleteOrderedFieldUniquenessDecodeBHist
              (cauchyCompleteOrderedFieldUniquenessEncodeBHist N))) =
          some
            (CauchyCompleteOrderedFieldUniquenessUp.mk
              K0 K1 R0 R1 Q0 Q1 D A0 A1 F0 F1 G H C P N)
      rw [cauchyCompleteOrderedFieldUniquenessDecode_encode K0,
        cauchyCompleteOrderedFieldUniquenessDecode_encode K1,
        cauchyCompleteOrderedFieldUniquenessDecode_encode R0,
        cauchyCompleteOrderedFieldUniquenessDecode_encode R1,
        cauchyCompleteOrderedFieldUniquenessDecode_encode Q0,
        cauchyCompleteOrderedFieldUniquenessDecode_encode Q1,
        cauchyCompleteOrderedFieldUniquenessDecode_encode D,
        cauchyCompleteOrderedFieldUniquenessDecode_encode A0,
        cauchyCompleteOrderedFieldUniquenessDecode_encode A1,
        cauchyCompleteOrderedFieldUniquenessDecode_encode F0,
        cauchyCompleteOrderedFieldUniquenessDecode_encode F1,
        cauchyCompleteOrderedFieldUniquenessDecode_encode G,
        cauchyCompleteOrderedFieldUniquenessDecode_encode H,
        cauchyCompleteOrderedFieldUniquenessDecode_encode C,
        cauchyCompleteOrderedFieldUniquenessDecode_encode P,
        cauchyCompleteOrderedFieldUniquenessDecode_encode N]

private theorem cauchyCompleteOrderedFieldUniquenessToEventFlow_injective
    {x y : CauchyCompleteOrderedFieldUniquenessUp} :
    cauchyCompleteOrderedFieldUniquenessToEventFlow x =
      cauchyCompleteOrderedFieldUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompleteOrderedFieldUniquenessFromEventFlow
          (cauchyCompleteOrderedFieldUniquenessToEventFlow x) =
        cauchyCompleteOrderedFieldUniquenessFromEventFlow
          (cauchyCompleteOrderedFieldUniquenessToEventFlow y) :=
    congrArg cauchyCompleteOrderedFieldUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompleteOrderedFieldUniqueness_round_trip x).symm
      (Eq.trans hread (cauchyCompleteOrderedFieldUniqueness_round_trip y)))

instance cauchyCompleteOrderedFieldUniquenessBHistCarrier :
    BHistCarrier CauchyCompleteOrderedFieldUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompleteOrderedFieldUniquenessToEventFlow
  fromEventFlow := cauchyCompleteOrderedFieldUniquenessFromEventFlow

instance cauchyCompleteOrderedFieldUniquenessChapterTasteGate :
    ChapterTasteGate CauchyCompleteOrderedFieldUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompleteOrderedFieldUniquenessFromEventFlow
        (cauchyCompleteOrderedFieldUniquenessToEventFlow x) = some x
    exact cauchyCompleteOrderedFieldUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompleteOrderedFieldUniquenessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompleteOrderedFieldUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompleteOrderedFieldUniquenessChapterTasteGate

theorem CauchyCompleteOrderedFieldUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompleteOrderedFieldUniquenessDecodeBHist
        (cauchyCompleteOrderedFieldUniquenessEncodeBHist h) = h) ∧
      (∀ x : CauchyCompleteOrderedFieldUniquenessUp,
        cauchyCompleteOrderedFieldUniquenessFromEventFlow
          (cauchyCompleteOrderedFieldUniquenessToEventFlow x) = some x) ∧
      (∀ x y : CauchyCompleteOrderedFieldUniquenessUp,
        cauchyCompleteOrderedFieldUniquenessToEventFlow x =
          cauchyCompleteOrderedFieldUniquenessToEventFlow y → x = y) ∧
      cauchyCompleteOrderedFieldUniquenessEncodeBHist BHist.Empty =
        ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyCompleteOrderedFieldUniquenessDecode_encode,
      cauchyCompleteOrderedFieldUniqueness_round_trip,
      fun _ _ heq => cauchyCompleteOrderedFieldUniquenessToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyCompleteOrderedFieldUniquenessUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRegularizationUp : Type where
  | mk : (Q D S A E H C P N : BHist) → RegularCauchyRegularizationUp
  deriving DecidableEq

def regularCauchyRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRegularizationEncodeBHist h

def regularCauchyRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRegularizationDecodeBHist tail)

private theorem regularCauchyRegularizationDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyRegularizationDecodeBHist
        (regularCauchyRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRegularizationFields : RegularCauchyRegularizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRegularizationUp.mk Q D S A E H C P N => [Q, D, S, A, E, H, C, P, N]

def regularCauchyRegularizationToEventFlow :
    RegularCauchyRegularizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyRegularizationFields x).map regularCauchyRegularizationEncodeBHist

private def regularCauchyRegularizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyRegularizationEventAtDefault index rest

def regularCauchyRegularizationFromEventFlow :
    EventFlow → Option RegularCauchyRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyRegularizationUp.mk
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 0 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 1 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 2 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 3 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 4 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 5 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 6 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 7 ef))
        (regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEventAtDefault 8 ef)))

private theorem regularCauchyRegularization_round_trip :
    ∀ x : RegularCauchyRegularizationUp,
      regularCauchyRegularizationFromEventFlow
        (regularCauchyRegularizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S A E H C P N =>
      change
        some
          (RegularCauchyRegularizationUp.mk
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist Q))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist D))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist S))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist A))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist E))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist H))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist C))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist P))
            (regularCauchyRegularizationDecodeBHist
              (regularCauchyRegularizationEncodeBHist N))) =
          some (RegularCauchyRegularizationUp.mk Q D S A E H C P N)
      rw [regularCauchyRegularizationDecode_encode_bhist Q,
        regularCauchyRegularizationDecode_encode_bhist D,
        regularCauchyRegularizationDecode_encode_bhist S,
        regularCauchyRegularizationDecode_encode_bhist A,
        regularCauchyRegularizationDecode_encode_bhist E,
        regularCauchyRegularizationDecode_encode_bhist H,
        regularCauchyRegularizationDecode_encode_bhist C,
        regularCauchyRegularizationDecode_encode_bhist P,
        regularCauchyRegularizationDecode_encode_bhist N]

private theorem regularCauchyRegularizationToEventFlow_injective
    {x y : RegularCauchyRegularizationUp} :
    regularCauchyRegularizationToEventFlow x =
      regularCauchyRegularizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRegularizationFromEventFlow
          (regularCauchyRegularizationToEventFlow x) =
        regularCauchyRegularizationFromEventFlow
          (regularCauchyRegularizationToEventFlow y) :=
    congrArg regularCauchyRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyRegularization_round_trip x).symm
      (Eq.trans hread (regularCauchyRegularization_round_trip y)))

instance regularCauchyRegularizationBHistCarrier :
    BHistCarrier RegularCauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRegularizationToEventFlow
  fromEventFlow := regularCauchyRegularizationFromEventFlow

instance regularCauchyRegularizationChapterTasteGate :
    ChapterTasteGate RegularCauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyRegularizationFromEventFlow
          (regularCauchyRegularizationToEventFlow x) =
        some x
    exact regularCauchyRegularization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyRegularizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyRegularizationChapterTasteGate

theorem RegularCauchyRegularizationTasteGate_single_carrier_alignment :
    regularCauchyRegularizationEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      (∀ h : BHist,
        regularCauchyRegularizationDecodeBHist
          (regularCauchyRegularizationEncodeBHist h) = h) ∧
        ChapterTasteGate RegularCauchyRegularizationUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, regularCauchyRegularizationDecode_encode_bhist,
      regularCauchyRegularizationChapterTasteGate⟩

end BEDC.Derived.RegularCauchyRegularizationUp

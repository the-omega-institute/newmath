import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ParsevalUp : Type where
  | mk (F S I E R D L H C P N : BHist) : ParsevalUp
  deriving DecidableEq

def parsevalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: parsevalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: parsevalEncodeBHist h

def parsevalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (parsevalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (parsevalDecodeBHist tail)

private theorem parsevalDecode_encode :
    ∀ h : BHist, parsevalDecodeBHist (parsevalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def parsevalToEventFlow : ParsevalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ParsevalUp.mk F S I E R D L H C P N =>
      [parsevalEncodeBHist F,
        parsevalEncodeBHist S,
        parsevalEncodeBHist I,
        parsevalEncodeBHist E,
        parsevalEncodeBHist R,
        parsevalEncodeBHist D,
        parsevalEncodeBHist L,
        parsevalEncodeBHist H,
        parsevalEncodeBHist C,
        parsevalEncodeBHist P,
        parsevalEncodeBHist N]

private def parsevalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => parsevalEventAtDefault index rest

def parsevalFromEventFlow : EventFlow → Option ParsevalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
      some
        (ParsevalUp.mk
          (parsevalDecodeBHist (parsevalEventAtDefault 0 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 1 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 2 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 3 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 4 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 5 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 6 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 7 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 8 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 9 ef))
          (parsevalDecodeBHist (parsevalEventAtDefault 10 ef)))

private theorem parseval_round_trip :
    ∀ x : ParsevalUp, parsevalFromEventFlow (parsevalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S I E R D L H C P N =>
      change
        some
          (ParsevalUp.mk
            (parsevalDecodeBHist (parsevalEncodeBHist F))
            (parsevalDecodeBHist (parsevalEncodeBHist S))
            (parsevalDecodeBHist (parsevalEncodeBHist I))
            (parsevalDecodeBHist (parsevalEncodeBHist E))
            (parsevalDecodeBHist (parsevalEncodeBHist R))
            (parsevalDecodeBHist (parsevalEncodeBHist D))
            (parsevalDecodeBHist (parsevalEncodeBHist L))
            (parsevalDecodeBHist (parsevalEncodeBHist H))
            (parsevalDecodeBHist (parsevalEncodeBHist C))
            (parsevalDecodeBHist (parsevalEncodeBHist P))
            (parsevalDecodeBHist (parsevalEncodeBHist N))) =
          some (ParsevalUp.mk F S I E R D L H C P N)
      rw [parsevalDecode_encode F,
        parsevalDecode_encode S,
        parsevalDecode_encode I,
        parsevalDecode_encode E,
        parsevalDecode_encode R,
        parsevalDecode_encode D,
        parsevalDecode_encode L,
        parsevalDecode_encode H,
        parsevalDecode_encode C,
        parsevalDecode_encode P,
        parsevalDecode_encode N]

private theorem parsevalToEventFlow_injective {x y : ParsevalUp} :
    parsevalToEventFlow x = parsevalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      parsevalFromEventFlow (parsevalToEventFlow x) =
        parsevalFromEventFlow (parsevalToEventFlow y) :=
    congrArg parsevalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (parseval_round_trip x).symm (Eq.trans hread (parseval_round_trip y)))

def parsevalFields : ParsevalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ParsevalUp.mk F S I E R D L H C P N => [F, S, I, E, R, D, L, H, C, P, N]

private theorem parseval_field_faithful :
    ∀ x y : ParsevalUp, parsevalFields x = parsevalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 S1 I1 E1 R1 D1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 S2 I2 E2 R2 D2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance parsevalBHistCarrier : BHistCarrier ParsevalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := parsevalToEventFlow
  fromEventFlow := parsevalFromEventFlow

instance parsevalChapterTasteGate : ChapterTasteGate ParsevalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change parsevalFromEventFlow (parsevalToEventFlow x) = some x
    exact parseval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (parsevalToEventFlow_injective heq)

instance parsevalFieldFaithful : FieldFaithful ParsevalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := parsevalFields
  field_faithful := parseval_field_faithful

theorem ParsevalTasteGate_single_carrier_alignment :
    (∀ h : BHist, parsevalDecodeBHist (parsevalEncodeBHist h) = h) ∧
      (∀ x : ParsevalUp, parsevalFromEventFlow (parsevalToEventFlow x) = some x) ∧
      (∀ x y : ParsevalUp, parsevalToEventFlow x = parsevalToEventFlow y → x = y) ∧
      parsevalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨parsevalDecode_encode,
      parseval_round_trip,
      fun _ _ heq => parsevalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ParsevalUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedReflectionUniversalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedReflectionUniversalUp : Type where
  | mk : (S M H F Q T R P N : BHist) → SeparatedReflectionUniversalUp
  deriving DecidableEq

def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

def decodeBHist : RawEvent → Option BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some BHist.Empty
  | BMark.b0 :: tail =>
      match decodeBHist tail with
      | some h => some (BHist.e0 h)
      | none => none
  | BMark.b1 :: tail =>
      match decodeBHist tail with
      | some h => some (BHist.e1 h)
      | none => none

private def SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal tail)

theorem SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decode_encode :
    ∀ w : BHist, decodeBHist (encodeBHist w) = some w := by
  -- BEDC touchpoint anchor: BHist BMark
  intro w
  induction w with
  | Empty => rfl
  | e0 h ih =>
      change
        (match decodeBHist (encodeBHist h) with
        | some h => some (BHist.e0 h)
        | none => none) = some (BHist.e0 h)
      rw [ih]
  | e1 h ih =>
      change
        (match decodeBHist (encodeBHist h) with
        | some h => some (BHist.e1 h)
        | none => none) = some (BHist.e1 h)
      rw [ih]

private theorem SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode :
    ∀ w : BHist,
      SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
        (encodeBHist w) = w := by
  -- BEDC touchpoint anchor: BHist BMark
  intro w
  induction w with
  | Empty => rfl
  | e0 h ih =>
      change
        BHist.e0
            (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
              (encodeBHist h)) =
          BHist.e0 h
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      change
        BHist.e1
            (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
              (encodeBHist h)) =
          BHist.e1 h
      exact congrArg BHist.e1 ih

def separatedReflectionUniversalFields : SeparatedReflectionUniversalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedReflectionUniversalUp.mk S M H F Q T R P N => [S, M, H, F, Q, T, R, P, N]

def separatedReflectionUniversalToEventFlow : SeparatedReflectionUniversalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedReflectionUniversalUp.mk S M H F Q T R P N =>
      [encodeBHist S, encodeBHist M, encodeBHist H, encodeBHist F, encodeBHist Q,
        encodeBHist T, encodeBHist R, encodeBHist P, encodeBHist N]

private def separatedReflectionUniversalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedReflectionUniversalEventAtDefault index rest

def separatedReflectionUniversalFromEventFlow :
    EventFlow → Option SeparatedReflectionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SeparatedReflectionUniversalUp.mk
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 0 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 1 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 2 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 3 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 4 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 5 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 6 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 7 ef))
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
          (separatedReflectionUniversalEventAtDefault 8 ef)))

private theorem SeparatedReflectionUniversalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedReflectionUniversalUp,
      separatedReflectionUniversalFromEventFlow
        (separatedReflectionUniversalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M H F Q T R P N =>
      change
        some
            (SeparatedReflectionUniversalUp.mk
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist S))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist M))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist H))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist F))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist Q))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist T))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist R))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist P))
              (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decodeBHistTotal
                (encodeBHist N))) =
          some (SeparatedReflectionUniversalUp.mk S M H F Q T R P N)
      rw [
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode S,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode M,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode H,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode F,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode Q,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode T,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode R,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode P,
        SeparatedReflectionUniversalTasteGate_single_carrier_alignment_total_decode_encode N]

private theorem SeparatedReflectionUniversalTasteGate_single_carrier_alignment_injective
    {x y : SeparatedReflectionUniversalUp} :
    separatedReflectionUniversalToEventFlow x = separatedReflectionUniversalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedReflectionUniversalFromEventFlow (separatedReflectionUniversalToEventFlow x) =
        separatedReflectionUniversalFromEventFlow (separatedReflectionUniversalToEventFlow y) :=
    congrArg separatedReflectionUniversalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_round_trip y)))

private theorem separatedReflectionUniversal_field_faithful :
    ∀ x y : SeparatedReflectionUniversalUp,
      separatedReflectionUniversalFields x = separatedReflectionUniversalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ M₁ H₁ F₁ Q₁ T₁ R₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ H₂ F₂ Q₂ T₂ R₂ P₂ N₂ =>
          cases h
          rfl

instance separatedReflectionUniversalBHistCarrier :
    BHistCarrier SeparatedReflectionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedReflectionUniversalToEventFlow
  fromEventFlow := separatedReflectionUniversalFromEventFlow

instance separatedReflectionUniversalChapterTasteGate :
    ChapterTasteGate SeparatedReflectionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedReflectionUniversalFromEventFlow
        (separatedReflectionUniversalToEventFlow x) = some x
    exact SeparatedReflectionUniversalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparatedReflectionUniversalTasteGate_single_carrier_alignment_injective heq)

instance separatedReflectionUniversalFieldFaithful :
    FieldFaithful SeparatedReflectionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedReflectionUniversalFields
  field_faithful := separatedReflectionUniversal_field_faithful

instance separatedReflectionUniversalInhabited : Inhabited SeparatedReflectionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    SeparatedReflectionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

instance separatedReflectionUniversalNontrivial : Nontrivial SeparatedReflectionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedReflectionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedReflectionUniversalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedReflectionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedReflectionUniversalChapterTasteGate

theorem SeparatedReflectionUniversalTasteGate_single_carrier_alignment :
    (∀ w : BHist, decodeBHist (encodeBHist w) = some w) ∧
      separatedReflectionUniversalToEventFlow
          (SeparatedReflectionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty,
          encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty,
          encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty] ∧
      (∀ x : SeparatedReflectionUniversalUp,
        separatedReflectionUniversalFromEventFlow
          (separatedReflectionUniversalToEventFlow x) = some x) ∧
      (∀ x y : SeparatedReflectionUniversalUp,
        separatedReflectionUniversalFields x = separatedReflectionUniversalFields y → x = y) ∧
      (separatedReflectionUniversalFields
          (SeparatedReflectionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)).length = 9 := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact SeparatedReflectionUniversalTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · constructor
      · exact SeparatedReflectionUniversalTasteGate_single_carrier_alignment_round_trip
      · constructor
        · exact separatedReflectionUniversal_field_faithful
        · rfl

end BEDC.Derived.SeparatedReflectionUniversalUp

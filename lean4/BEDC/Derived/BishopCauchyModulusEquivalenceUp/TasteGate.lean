import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyModulusEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyModulusEquivalenceUp : Type where
  | mk (Q D S R E K U H T P N : BHist) : BishopCauchyModulusEquivalenceUp
  deriving DecidableEq

def bishopCauchyModulusEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyModulusEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyModulusEquivalenceEncodeBHist h

def bishopCauchyModulusEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyModulusEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyModulusEquivalenceDecodeBHist tail)

private theorem bishopCauchyModulusEquivalence_decode_encode_bhist :
    ∀ h : BHist,
      bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyModulusEquivalenceToEventFlow :
    BishopCauchyModulusEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyModulusEquivalenceUp.mk Q D S R E K U H T P N =>
      [bishopCauchyModulusEquivalenceEncodeBHist Q,
        bishopCauchyModulusEquivalenceEncodeBHist D,
        bishopCauchyModulusEquivalenceEncodeBHist S,
        bishopCauchyModulusEquivalenceEncodeBHist R,
        bishopCauchyModulusEquivalenceEncodeBHist E,
        bishopCauchyModulusEquivalenceEncodeBHist K,
        bishopCauchyModulusEquivalenceEncodeBHist U,
        bishopCauchyModulusEquivalenceEncodeBHist H,
        bishopCauchyModulusEquivalenceEncodeBHist T,
        bishopCauchyModulusEquivalenceEncodeBHist P,
        bishopCauchyModulusEquivalenceEncodeBHist N]

private def bishopCauchyModulusEquivalenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCauchyModulusEquivalenceEventAtDefault index rest

def bishopCauchyModulusEquivalenceFromEventFlow
    (ef : EventFlow) : Option BishopCauchyModulusEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyModulusEquivalenceUp.mk
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 0 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 1 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 2 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 3 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 4 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 5 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 6 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 7 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 8 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 9 ef))
      (bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEventAtDefault 10 ef)))

private theorem bishopCauchyModulusEquivalence_round_trip :
    ∀ x : BishopCauchyModulusEquivalenceUp,
      bishopCauchyModulusEquivalenceFromEventFlow
        (bishopCauchyModulusEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D S R E K U H T P N =>
      change
        some
          (BishopCauchyModulusEquivalenceUp.mk
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist Q))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist D))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist S))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist R))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist E))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist K))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist U))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist H))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist T))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist P))
            (bishopCauchyModulusEquivalenceDecodeBHist
              (bishopCauchyModulusEquivalenceEncodeBHist N))) =
          some (BishopCauchyModulusEquivalenceUp.mk Q D S R E K U H T P N)
      rw [bishopCauchyModulusEquivalence_decode_encode_bhist Q,
        bishopCauchyModulusEquivalence_decode_encode_bhist D,
        bishopCauchyModulusEquivalence_decode_encode_bhist S,
        bishopCauchyModulusEquivalence_decode_encode_bhist R,
        bishopCauchyModulusEquivalence_decode_encode_bhist E,
        bishopCauchyModulusEquivalence_decode_encode_bhist K,
        bishopCauchyModulusEquivalence_decode_encode_bhist U,
        bishopCauchyModulusEquivalence_decode_encode_bhist H,
        bishopCauchyModulusEquivalence_decode_encode_bhist T,
        bishopCauchyModulusEquivalence_decode_encode_bhist P,
        bishopCauchyModulusEquivalence_decode_encode_bhist N]

private theorem bishopCauchyModulusEquivalenceToEventFlow_injective
    {x y : BishopCauchyModulusEquivalenceUp} :
    bishopCauchyModulusEquivalenceToEventFlow x =
      bishopCauchyModulusEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyModulusEquivalenceFromEventFlow
          (bishopCauchyModulusEquivalenceToEventFlow x) =
        bishopCauchyModulusEquivalenceFromEventFlow
          (bishopCauchyModulusEquivalenceToEventFlow y) :=
    congrArg bishopCauchyModulusEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchyModulusEquivalence_round_trip x).symm
      (Eq.trans hread (bishopCauchyModulusEquivalence_round_trip y)))

instance bishopCauchyModulusEquivalenceBHistCarrier :
    BHistCarrier BishopCauchyModulusEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyModulusEquivalenceToEventFlow
  fromEventFlow := bishopCauchyModulusEquivalenceFromEventFlow

instance bishopCauchyModulusEquivalenceChapterTasteGate :
    ChapterTasteGate BishopCauchyModulusEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyModulusEquivalenceFromEventFlow
        (bishopCauchyModulusEquivalenceToEventFlow x) = some x
    exact bishopCauchyModulusEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyModulusEquivalenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyModulusEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyModulusEquivalenceChapterTasteGate

theorem BishopCauchyModulusEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyModulusEquivalenceDecodeBHist
        (bishopCauchyModulusEquivalenceEncodeBHist h) = h) ∧
      (∀ x : BishopCauchyModulusEquivalenceUp,
        bishopCauchyModulusEquivalenceFromEventFlow
          (bishopCauchyModulusEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : BishopCauchyModulusEquivalenceUp,
          bishopCauchyModulusEquivalenceToEventFlow x =
            bishopCauchyModulusEquivalenceToEventFlow y → x = y) ∧
          bishopCauchyModulusEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopCauchyModulusEquivalence_decode_encode_bhist
  · constructor
    · exact bishopCauchyModulusEquivalence_round_trip
    · constructor
      · intro x y heq
        exact bishopCauchyModulusEquivalenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopCauchyModulusEquivalenceUp

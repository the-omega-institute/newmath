import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealUniformCompletionUp : Type where
  | mk (R U J T S D Q H C P N : BHist) : BishopRealUniformCompletionUp
  deriving DecidableEq

def bishopRealUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealUniformCompletionEncodeBHist h

def bishopRealUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealUniformCompletionDecodeBHist tail)

private theorem BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealUniformCompletionFields : BishopRealUniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealUniformCompletionUp.mk R U J T S D Q H C P N =>
      [R, U, J, T, S, D, Q, H, C, P, N]

def bishopRealUniformCompletionToEventFlow : BishopRealUniformCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bishopRealUniformCompletionEncodeBHist (bishopRealUniformCompletionFields x)

private def bishopRealUniformCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealUniformCompletionRawAt index rest

def bishopRealUniformCompletionFromEventFlow : EventFlow → Option BishopRealUniformCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (BishopRealUniformCompletionUp.mk
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 0 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 1 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 2 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 3 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 4 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 5 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 6 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 7 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 8 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 9 flow))
          (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionRawAt 10 flow)))

private theorem BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealUniformCompletionUp,
      bishopRealUniformCompletionFromEventFlow
        (bishopRealUniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R U J T S D Q H C P N =>
      change
        some
          (BishopRealUniformCompletionUp.mk
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist R))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist U))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist J))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist T))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist S))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist D))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist Q))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist H))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist C))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist P))
            (bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist N))) =
          some (BishopRealUniformCompletionUp.mk R U J T S D Q H C P N)
      rw [BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode R,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode U,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode J,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode T,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode S,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode D,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode Q,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode H,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode C,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode P,
        BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode N]

private theorem BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealUniformCompletionUp} :
    bishopRealUniformCompletionToEventFlow x = bishopRealUniformCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealUniformCompletionFromEventFlow (bishopRealUniformCompletionToEventFlow x) =
        bishopRealUniformCompletionFromEventFlow (bishopRealUniformCompletionToEventFlow y) :=
    congrArg bishopRealUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRealUniformCompletionBHistCarrier :
    BHistCarrier BishopRealUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealUniformCompletionToEventFlow
  fromEventFlow := bishopRealUniformCompletionFromEventFlow

instance bishopRealUniformCompletionChapterTasteGate :
    ChapterTasteGate BishopRealUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealUniformCompletionFromEventFlow
        (bishopRealUniformCompletionToEventFlow x) = some x
    exact BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopRealUniformCompletionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRealUniformCompletionDecodeBHist (bishopRealUniformCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopRealUniformCompletionUp,
        bishopRealUniformCompletionFromEventFlow
          (bishopRealUniformCompletionToEventFlow x) = some x) ∧
        (∀ x y : BishopRealUniformCompletionUp,
          bishopRealUniformCompletionToEventFlow x =
            bishopRealUniformCompletionToEventFlow y → x = y) ∧
          bishopRealUniformCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_decode,
      BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact BishopRealUniformCompletionUpTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.BishopRealUniformCompletionUp

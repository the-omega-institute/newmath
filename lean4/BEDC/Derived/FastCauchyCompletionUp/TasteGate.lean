import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyCompletionUp : Type where
  | mk (M S D Q E H C P N : BHist) : FastCauchyCompletionUp
  deriving DecidableEq

def fastCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyCompletionEncodeBHist h

def fastCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyCompletionDecodeBHist tail)

private theorem fastCauchyCompletion_decode_encode_bhist :
    ∀ h : BHist, fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchyCompletionFields : FastCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchyCompletionUp.mk M S D Q E H C P N => [M, S, D, Q, E, H, C, P, N]

def fastCauchyCompletionToEventFlow : FastCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fastCauchyCompletionFields x).map fastCauchyCompletionEncodeBHist

private def fastCauchyCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fastCauchyCompletionRawAt n rest

private def fastCauchyCompletionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fastCauchyCompletionLengthEq n rest

def fastCauchyCompletionFromEventFlow : EventFlow → Option FastCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match fastCauchyCompletionLengthEq 9 flow with
      | true =>
          some
            (FastCauchyCompletionUp.mk
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 0 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 1 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 2 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 3 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 4 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 5 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 6 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 7 flow))
              (fastCauchyCompletionDecodeBHist (fastCauchyCompletionRawAt 8 flow)))
      | false => none

private theorem fastCauchyCompletion_round_trip :
    ∀ x : FastCauchyCompletionUp,
      fastCauchyCompletionFromEventFlow (fastCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D Q E H C P N =>
      change
        some
          (FastCauchyCompletionUp.mk
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist M))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist S))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist D))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist Q))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist E))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist H))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist C))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist P))
            (fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist N))) =
          some (FastCauchyCompletionUp.mk M S D Q E H C P N)
      rw [fastCauchyCompletion_decode_encode_bhist M,
        fastCauchyCompletion_decode_encode_bhist S,
        fastCauchyCompletion_decode_encode_bhist D,
        fastCauchyCompletion_decode_encode_bhist Q,
        fastCauchyCompletion_decode_encode_bhist E,
        fastCauchyCompletion_decode_encode_bhist H,
        fastCauchyCompletion_decode_encode_bhist C,
        fastCauchyCompletion_decode_encode_bhist P,
        fastCauchyCompletion_decode_encode_bhist N]

private theorem fastCauchyCompletionToEventFlow_injective {x y : FastCauchyCompletionUp} :
    fastCauchyCompletionToEventFlow x = fastCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchyCompletionFromEventFlow (fastCauchyCompletionToEventFlow x) =
        fastCauchyCompletionFromEventFlow (fastCauchyCompletionToEventFlow y) :=
    congrArg fastCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastCauchyCompletion_round_trip x).symm
      (Eq.trans hread (fastCauchyCompletion_round_trip y)))

instance fastCauchyCompletionBHistCarrier : BHistCarrier FastCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyCompletionToEventFlow
  fromEventFlow := fastCauchyCompletionFromEventFlow

instance fastCauchyCompletionChapterTasteGate : ChapterTasteGate FastCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchyCompletionFromEventFlow (fastCauchyCompletionToEventFlow x) = some x
    exact fastCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastCauchyCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FastCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fastCauchyCompletionChapterTasteGate

theorem FastCauchyCompletionUp_single_carrier_alignment :
    (forall h : BHist, fastCauchyCompletionDecodeBHist (fastCauchyCompletionEncodeBHist h) = h) ∧
      (forall x : FastCauchyCompletionUp,
        fastCauchyCompletionFromEventFlow (fastCauchyCompletionToEventFlow x) = some x) ∧
      (forall x y : FastCauchyCompletionUp,
        fastCauchyCompletionToEventFlow x = fastCauchyCompletionToEventFlow y -> x = y) ∧
      fastCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨fastCauchyCompletion_decode_encode_bhist,
      fastCauchyCompletion_round_trip,
      (fun _ _ heq => fastCauchyCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FastCauchyCompletionUp

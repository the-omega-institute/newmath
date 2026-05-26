import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConcaveModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConcaveModulusUp : Type where
  | mk (Q D M J S H C P N : BHist) : ConcaveModulusUp
  deriving DecidableEq

def concaveModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: concaveModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: concaveModulusEncodeBHist h

def concaveModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (concaveModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (concaveModulusDecodeBHist tail)

private theorem concaveModulusDecodeEncodeBHist :
    ∀ h : BHist, concaveModulusDecodeBHist (concaveModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def concaveModulusToEventFlow : ConcaveModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConcaveModulusUp.mk Q D M J S H C P N =>
      [concaveModulusEncodeBHist Q,
        concaveModulusEncodeBHist D,
        concaveModulusEncodeBHist M,
        concaveModulusEncodeBHist J,
        concaveModulusEncodeBHist S,
        concaveModulusEncodeBHist H,
        concaveModulusEncodeBHist C,
        concaveModulusEncodeBHist P,
        concaveModulusEncodeBHist N]

private def concaveModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => concaveModulusRawAt n rest

private def concaveModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => concaveModulusLengthEq n rest

def concaveModulusFromEventFlow : EventFlow → Option ConcaveModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match concaveModulusLengthEq 9 flow with
      | true =>
          some
            (ConcaveModulusUp.mk
              (concaveModulusDecodeBHist (concaveModulusRawAt 0 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 1 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 2 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 3 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 4 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 5 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 6 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 7 flow))
              (concaveModulusDecodeBHist (concaveModulusRawAt 8 flow)))
      | false => none

private theorem concaveModulus_round_trip :
    ∀ x : ConcaveModulusUp,
      concaveModulusFromEventFlow (concaveModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D M J S H C P N =>
      change
        some
          (ConcaveModulusUp.mk
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist Q))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist D))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist M))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist J))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist S))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist H))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist C))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist P))
            (concaveModulusDecodeBHist (concaveModulusEncodeBHist N))) =
          some (ConcaveModulusUp.mk Q D M J S H C P N)
      rw [concaveModulusDecodeEncodeBHist Q,
        concaveModulusDecodeEncodeBHist D,
        concaveModulusDecodeEncodeBHist M,
        concaveModulusDecodeEncodeBHist J,
        concaveModulusDecodeEncodeBHist S,
        concaveModulusDecodeEncodeBHist H,
        concaveModulusDecodeEncodeBHist C,
        concaveModulusDecodeEncodeBHist P,
        concaveModulusDecodeEncodeBHist N]

private theorem concaveModulusToEventFlow_injective {x y : ConcaveModulusUp} :
    concaveModulusToEventFlow x = concaveModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      concaveModulusFromEventFlow (concaveModulusToEventFlow x) =
        concaveModulusFromEventFlow (concaveModulusToEventFlow y) :=
    congrArg concaveModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (concaveModulus_round_trip x).symm
      (Eq.trans hread (concaveModulus_round_trip y)))

instance concaveModulusBHistCarrier : BHistCarrier ConcaveModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := concaveModulusToEventFlow
  fromEventFlow := concaveModulusFromEventFlow

instance concaveModulusChapterTasteGate : ChapterTasteGate ConcaveModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change concaveModulusFromEventFlow (concaveModulusToEventFlow x) = some x
    exact concaveModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (concaveModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConcaveModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  concaveModulusChapterTasteGate

theorem ConcaveModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, concaveModulusDecodeBHist (concaveModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConcaveModulusUp) ∧
        Nonempty (ChapterTasteGate ConcaveModulusUp) ∧
          (∀ x : ConcaveModulusUp,
            concaveModulusFromEventFlow (concaveModulusToEventFlow x) = some x) ∧
            (∀ x y : ConcaveModulusUp,
              concaveModulusToEventFlow x = concaveModulusToEventFlow y → x = y) ∧
              concaveModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨concaveModulusDecodeEncodeBHist,
      ⟨concaveModulusBHistCarrier⟩,
      ⟨concaveModulusChapterTasteGate⟩,
      concaveModulus_round_trip,
      (fun _ _ heq => concaveModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ConcaveModulusUp

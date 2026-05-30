import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalConvergenceUp : Type where
  | mk (S A M U R E H C P L : BHist) : NormalConvergenceUp
  deriving DecidableEq

def normalConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalConvergenceEncodeBHist h

def normalConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalConvergenceDecodeBHist tail)

private theorem normalConvergence_decode_encode_bhist :
    ∀ h : BHist, normalConvergenceDecodeBHist (normalConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def normalConvergenceFields : NormalConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalConvergenceUp.mk S A M U R E H C P L => [S, A, M, U, R, E, H, C, P, L]

def normalConvergenceToEventFlow : NormalConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalConvergenceFields x).map normalConvergenceEncodeBHist

private def normalConvergenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => normalConvergenceRawAt n rest

private def normalConvergenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => normalConvergenceLengthEq n rest

def normalConvergenceFromEventFlow : EventFlow → Option NormalConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match normalConvergenceLengthEq 10 flow with
      | true =>
          some
            (NormalConvergenceUp.mk
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 0 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 1 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 2 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 3 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 4 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 5 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 6 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 7 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 8 flow))
              (normalConvergenceDecodeBHist (normalConvergenceRawAt 9 flow)))
      | false => none

private theorem normalConvergence_round_trip :
    ∀ x : NormalConvergenceUp,
      normalConvergenceFromEventFlow (normalConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A M U R E H C P L =>
      change
        some
          (NormalConvergenceUp.mk
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist S))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist A))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist M))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist U))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist R))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist E))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist H))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist C))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist P))
            (normalConvergenceDecodeBHist (normalConvergenceEncodeBHist L))) =
          some (NormalConvergenceUp.mk S A M U R E H C P L)
      rw [normalConvergence_decode_encode_bhist S,
        normalConvergence_decode_encode_bhist A,
        normalConvergence_decode_encode_bhist M,
        normalConvergence_decode_encode_bhist U,
        normalConvergence_decode_encode_bhist R,
        normalConvergence_decode_encode_bhist E,
        normalConvergence_decode_encode_bhist H,
        normalConvergence_decode_encode_bhist C,
        normalConvergence_decode_encode_bhist P,
        normalConvergence_decode_encode_bhist L]

private theorem normalConvergenceToEventFlow_injective {x y : NormalConvergenceUp} :
    normalConvergenceToEventFlow x = normalConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalConvergenceFromEventFlow (normalConvergenceToEventFlow x) =
        normalConvergenceFromEventFlow (normalConvergenceToEventFlow y) :=
    congrArg normalConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalConvergence_round_trip x).symm
      (Eq.trans hread (normalConvergence_round_trip y)))

instance normalConvergenceBHistCarrier : BHistCarrier NormalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalConvergenceToEventFlow
  fromEventFlow := normalConvergenceFromEventFlow

instance normalConvergenceChapterTasteGate : ChapterTasteGate NormalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalConvergenceFromEventFlow (normalConvergenceToEventFlow x) = some x
    exact normalConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NormalConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalConvergenceChapterTasteGate

theorem NormalConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, normalConvergenceDecodeBHist (normalConvergenceEncodeBHist h) = h) ∧
      (∀ x : NormalConvergenceUp,
        normalConvergenceFromEventFlow (normalConvergenceToEventFlow x) = some x) ∧
        (∀ x y : NormalConvergenceUp,
          normalConvergenceToEventFlow x = normalConvergenceToEventFlow y → x = y) ∧
          normalConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨normalConvergence_decode_encode_bhist,
      normalConvergence_round_trip,
      fun _ _ heq => normalConvergenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.NormalConvergenceUp

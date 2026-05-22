import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchySequenceUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchySequenceUp : Type where
  | mk (S Q D M R E H C P N : BHist) : UniformCauchySequenceUp
  deriving DecidableEq

def uniformCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchySequenceEncodeBHist h

def uniformCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchySequenceDecodeBHist tail)

private theorem uniformCauchySequence_decode_encode_bhist :
    ∀ h : BHist, uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchySequenceFields : UniformCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchySequenceUp.mk S Q D M R E H C P N => [S, Q, D, M, R, E, H, C, P, N]

def uniformCauchySequenceToEventFlow : UniformCauchySequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformCauchySequenceFields x).map uniformCauchySequenceEncodeBHist

private def uniformCauchySequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => uniformCauchySequenceRawAt n rest

def uniformCauchySequenceFromEventFlow (flow : EventFlow) : Option UniformCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchySequenceUp.mk
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 0 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 1 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 2 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 3 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 4 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 5 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 6 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 7 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 8 flow))
      (uniformCauchySequenceDecodeBHist (uniformCauchySequenceRawAt 9 flow)))

private theorem uniformCauchySequence_round_trip :
    ∀ x : UniformCauchySequenceUp,
      uniformCauchySequenceFromEventFlow (uniformCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D M R E H C P N =>
      change
        some
          (UniformCauchySequenceUp.mk
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist S))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist Q))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist D))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist M))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist R))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist E))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist H))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist C))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist P))
            (uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist N))) =
          some (UniformCauchySequenceUp.mk S Q D M R E H C P N)
      rw [uniformCauchySequence_decode_encode_bhist S,
        uniformCauchySequence_decode_encode_bhist Q,
        uniformCauchySequence_decode_encode_bhist D,
        uniformCauchySequence_decode_encode_bhist M,
        uniformCauchySequence_decode_encode_bhist R,
        uniformCauchySequence_decode_encode_bhist E,
        uniformCauchySequence_decode_encode_bhist H,
        uniformCauchySequence_decode_encode_bhist C,
        uniformCauchySequence_decode_encode_bhist P,
        uniformCauchySequence_decode_encode_bhist N]

private theorem uniformCauchySequenceToEventFlow_injective {x y : UniformCauchySequenceUp} :
    uniformCauchySequenceToEventFlow x = uniformCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchySequenceFromEventFlow (uniformCauchySequenceToEventFlow x) =
        uniformCauchySequenceFromEventFlow (uniformCauchySequenceToEventFlow y) :=
    congrArg uniformCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchySequence_round_trip x).symm
      (Eq.trans hread (uniformCauchySequence_round_trip y)))

private theorem uniformCauchySequence_fields_faithful :
    ∀ x y : UniformCauchySequenceUp, uniformCauchySequenceFields x = uniformCauchySequenceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ D₁ M₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ D₂ M₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance uniformCauchySequenceBHistCarrier : BHistCarrier UniformCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchySequenceToEventFlow
  fromEventFlow := uniformCauchySequenceFromEventFlow

instance uniformCauchySequenceChapterTasteGate :
    ChapterTasteGate UniformCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchySequenceFromEventFlow (uniformCauchySequenceToEventFlow x) = some x
    exact uniformCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchySequenceToEventFlow_injective heq)

instance uniformCauchySequenceFieldFaithful : FieldFaithful UniformCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchySequenceFields
  field_faithful := uniformCauchySequence_fields_faithful

instance uniformCauchySequenceNontrivial : Nontrivial UniformCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchySequenceChapterTasteGate

theorem UniformCauchySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformCauchySequenceDecodeBHist (uniformCauchySequenceEncodeBHist h) = h) ∧
      (∀ x : UniformCauchySequenceUp,
        uniformCauchySequenceFromEventFlow (uniformCauchySequenceToEventFlow x) = some x) ∧
        (∀ x y : UniformCauchySequenceUp,
          uniformCauchySequenceToEventFlow x = uniformCauchySequenceToEventFlow y → x = y) ∧
          uniformCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨uniformCauchySequence_decode_encode_bhist,
      uniformCauchySequence_round_trip,
      fun _ _ heq => uniformCauchySequenceToEventFlow_injective heq,
      rfl⟩

end TasteGate
end BEDC.Derived.UniformCauchySequenceUp

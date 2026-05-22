import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FareySequenceUp : Type where
  | mk (source pattern classifier stability ledger : BHist) : FareySequenceUp
  deriving DecidableEq

def fareySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fareySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fareySequenceEncodeBHist h

def fareySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fareySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fareySequenceDecodeBHist tail)

private theorem fareySequence_decode_encode_bhist :
    ∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fareySequenceFields : FareySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FareySequenceUp.mk source pattern classifier stability ledger =>
      [source, pattern, classifier, stability, ledger]

def fareySequenceToEventFlow : FareySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fareySequenceFields x).map fareySequenceEncodeBHist

private def fareySequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fareySequenceRawAt n rest

def fareySequenceFromEventFlow : EventFlow → Option FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (FareySequenceUp.mk
        (fareySequenceDecodeBHist (fareySequenceRawAt 0 flow))
        (fareySequenceDecodeBHist (fareySequenceRawAt 1 flow))
        (fareySequenceDecodeBHist (fareySequenceRawAt 2 flow))
        (fareySequenceDecodeBHist (fareySequenceRawAt 3 flow))
        (fareySequenceDecodeBHist (fareySequenceRawAt 4 flow)))

private theorem fareySequence_round_trip :
    ∀ x : FareySequenceUp,
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger =>
      change
        some
          (FareySequenceUp.mk
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist source))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist pattern))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist classifier))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist stability))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist ledger))) =
          some (FareySequenceUp.mk source pattern classifier stability ledger)
      rw [fareySequence_decode_encode_bhist source,
        fareySequence_decode_encode_bhist pattern,
        fareySequence_decode_encode_bhist classifier,
        fareySequence_decode_encode_bhist stability,
        fareySequence_decode_encode_bhist ledger]

private theorem fareySequenceToEventFlow_injective {x y : FareySequenceUp} :
    fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) =
        fareySequenceFromEventFlow (fareySequenceToEventFlow y) :=
    congrArg fareySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fareySequence_round_trip x).symm
      (Eq.trans hread (fareySequence_round_trip y)))

instance fareySequenceBHistCarrier : BHistCarrier FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fareySequenceToEventFlow
  fromEventFlow := fareySequenceFromEventFlow

instance fareySequenceChapterTasteGate : ChapterTasteGate FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x
    exact fareySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fareySequenceToEventFlow_injective heq)

instance fareySequenceFieldFaithful : FieldFaithful FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fareySequenceFields
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ pattern₁ classifier₁ stability₁ ledger₁ =>
      cases y with
      | mk source₂ pattern₂ classifier₂ stability₂ ledger₂ =>
        simp only [fareySequenceFields] at h
        injection h with hsource tail₁
        injection tail₁ with hpattern tail₂
        injection tail₂ with hclassifier tail₃
        injection tail₃ with hstability tail₄
        injection tail₄ with hledger _
        cases hsource
        cases hpattern
        cases hclassifier
        cases hstability
        cases hledger
        rfl

instance fareySequenceNontrivial : Nontrivial FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FareySequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FareySequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fareySequenceChapterTasteGate

theorem FareySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h) ∧
      (∀ x : FareySequenceUp,
        fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x) ∧
        (∀ x y : FareySequenceUp,
          fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y) ∧
          fareySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨fareySequence_decode_encode_bhist,
      ⟨fareySequence_round_trip,
        ⟨fun _ _ heq => fareySequenceToEventFlow_injective heq, rfl⟩⟩⟩

end BEDC.Derived.FareySequenceUp

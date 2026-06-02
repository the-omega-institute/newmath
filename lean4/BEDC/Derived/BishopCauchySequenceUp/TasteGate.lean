import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchySequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchySequenceUp : Type where
  | mk (S D X U R H C P N : BHist) : BishopCauchySequenceUp
  deriving DecidableEq

def bishopCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchySequenceEncodeBHist h

def bishopCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchySequenceDecodeBHist tail)

private theorem bishopCauchySequenceDecode_encode_bhist :
    ∀ h : BHist, bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchySequenceFields : BishopCauchySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchySequenceUp.mk S D X U R H C P N => [S, D, X, U, R, H, C, P, N]

def bishopCauchySequenceToEventFlow : BishopCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchySequenceFields x).map bishopCauchySequenceEncodeBHist

private def bishopCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchySequenceEventAt index rest

def bishopCauchySequenceFromEventFlow (ef : EventFlow) :
    Option BishopCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchySequenceUp.mk
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 0 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 1 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 2 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 3 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 4 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 5 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 6 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 7 ef))
      (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEventAt 8 ef)))

private theorem bishopCauchySequence_round_trip (x : BishopCauchySequenceUp) :
    bishopCauchySequenceFromEventFlow (bishopCauchySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D X U R H C P N =>
      change
        some
          (BishopCauchySequenceUp.mk
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist S))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist D))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist X))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist U))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist R))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist H))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist C))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist P))
            (bishopCauchySequenceDecodeBHist (bishopCauchySequenceEncodeBHist N))) =
          some (BishopCauchySequenceUp.mk S D X U R H C P N)
      rw [bishopCauchySequenceDecode_encode_bhist S,
        bishopCauchySequenceDecode_encode_bhist D,
        bishopCauchySequenceDecode_encode_bhist X,
        bishopCauchySequenceDecode_encode_bhist U,
        bishopCauchySequenceDecode_encode_bhist R,
        bishopCauchySequenceDecode_encode_bhist H,
        bishopCauchySequenceDecode_encode_bhist C,
        bishopCauchySequenceDecode_encode_bhist P,
        bishopCauchySequenceDecode_encode_bhist N]

private theorem bishopCauchySequenceToEventFlow_injective {x y : BishopCauchySequenceUp} :
    bishopCauchySequenceToEventFlow x = bishopCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchySequenceFromEventFlow (bishopCauchySequenceToEventFlow x) =
        bishopCauchySequenceFromEventFlow (bishopCauchySequenceToEventFlow y) :=
    congrArg bishopCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchySequence_round_trip x).symm
      (Eq.trans hread (bishopCauchySequence_round_trip y)))

instance bishopCauchySequenceBHistCarrier : BHistCarrier BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchySequenceToEventFlow
  fromEventFlow := bishopCauchySequenceFromEventFlow

instance bishopCauchySequenceChapterTasteGate :
    ChapterTasteGate BishopCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchySequenceFromEventFlow (bishopCauchySequenceToEventFlow x) = some x
    exact bishopCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchySequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchySequenceChapterTasteGate

theorem BishopCauchySequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopCauchySequenceUp) ∧
      Nonempty (ChapterTasteGate BishopCauchySequenceUp) ∧
        ∀ x y : BishopCauchySequenceUp,
          BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨bishopCauchySequenceBHistCarrier⟩
  · constructor
    · exact ⟨bishopCauchySequenceChapterTasteGate⟩
    · intro x y heq
      change bishopCauchySequenceToEventFlow x = bishopCauchySequenceToEventFlow y at heq
      exact bishopCauchySequenceToEventFlow_injective heq

end BEDC.Derived.BishopCauchySequenceUp

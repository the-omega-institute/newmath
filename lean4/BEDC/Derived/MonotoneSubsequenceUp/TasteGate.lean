import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneSubsequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneSubsequenceUp : Type where
  | mk
      (source selector cofinal selectedWindows dyadic regularHandoff realSeal transport
        continuation provenance name : BHist) :
      MonotoneSubsequenceUp
  deriving DecidableEq

def monotoneSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneSubsequenceEncodeBHist h

def monotoneSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneSubsequenceDecodeBHist tail)

private theorem monotoneSubsequence_decode_encode_bhist :
    ∀ h : BHist, monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneSubsequenceFields : MonotoneSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneSubsequenceUp.mk source selector cofinal selectedWindows dyadic regularHandoff
      realSeal transport continuation provenance name =>
      [source, selector, cofinal, selectedWindows, dyadic, regularHandoff, realSeal,
        transport, continuation, provenance, name]

def monotoneSubsequenceToEventFlow : MonotoneSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (monotoneSubsequenceFields x).map monotoneSubsequenceEncodeBHist

private def monotoneSubsequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneSubsequenceEventAtDefault index rest

def monotoneSubsequenceFromEventFlow (ef : EventFlow) : Option MonotoneSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneSubsequenceUp.mk
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 0 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 1 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 2 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 3 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 4 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 5 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 6 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 7 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 8 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 9 ef))
      (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEventAtDefault 10 ef)))

private theorem monotoneSubsequence_round_trip :
    ∀ x : MonotoneSubsequenceUp,
      monotoneSubsequenceFromEventFlow (monotoneSubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source selector cofinal selectedWindows dyadic regularHandoff realSeal transport
      continuation provenance name =>
      change
        some
          (MonotoneSubsequenceUp.mk
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist source))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist selector))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist cofinal))
            (monotoneSubsequenceDecodeBHist
              (monotoneSubsequenceEncodeBHist selectedWindows))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist dyadic))
            (monotoneSubsequenceDecodeBHist
              (monotoneSubsequenceEncodeBHist regularHandoff))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist realSeal))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist transport))
            (monotoneSubsequenceDecodeBHist
              (monotoneSubsequenceEncodeBHist continuation))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist provenance))
            (monotoneSubsequenceDecodeBHist (monotoneSubsequenceEncodeBHist name))) =
          some
            (MonotoneSubsequenceUp.mk source selector cofinal selectedWindows dyadic
              regularHandoff realSeal transport continuation provenance name)
      rw [monotoneSubsequence_decode_encode_bhist source,
        monotoneSubsequence_decode_encode_bhist selector,
        monotoneSubsequence_decode_encode_bhist cofinal,
        monotoneSubsequence_decode_encode_bhist selectedWindows,
        monotoneSubsequence_decode_encode_bhist dyadic,
        monotoneSubsequence_decode_encode_bhist regularHandoff,
        monotoneSubsequence_decode_encode_bhist realSeal,
        monotoneSubsequence_decode_encode_bhist transport,
        monotoneSubsequence_decode_encode_bhist continuation,
        monotoneSubsequence_decode_encode_bhist provenance,
        monotoneSubsequence_decode_encode_bhist name]

private theorem monotoneSubsequenceToEventFlow_injective {x y : MonotoneSubsequenceUp} :
    monotoneSubsequenceToEventFlow x = monotoneSubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneSubsequenceFromEventFlow (monotoneSubsequenceToEventFlow x) =
        monotoneSubsequenceFromEventFlow (monotoneSubsequenceToEventFlow y) :=
    congrArg monotoneSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneSubsequence_round_trip x).symm
      (Eq.trans hread (monotoneSubsequence_round_trip y)))

instance monotoneSubsequenceBHistCarrier : BHistCarrier MonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneSubsequenceToEventFlow
  fromEventFlow := monotoneSubsequenceFromEventFlow

instance monotoneSubsequenceChapterTasteGate : ChapterTasteGate MonotoneSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monotoneSubsequenceFromEventFlow (monotoneSubsequenceToEventFlow x) = some x
    exact monotoneSubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneSubsequenceToEventFlow_injective heq)

theorem MonotoneSubsequenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier MonotoneSubsequenceUp) ∧
      Nonempty (ChapterTasteGate MonotoneSubsequenceUp) ∧
        ∃ x : MonotoneSubsequenceUp,
          BHistCarrier.toEventFlow x =
            monotoneSubsequenceToEventFlow
              (MonotoneSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨monotoneSubsequenceBHistCarrier⟩,
      ⟨⟨monotoneSubsequenceChapterTasteGate⟩,
        ⟨MonotoneSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          rfl⟩⟩⟩

end BEDC.Derived.MonotoneSubsequenceUp.TasteGate

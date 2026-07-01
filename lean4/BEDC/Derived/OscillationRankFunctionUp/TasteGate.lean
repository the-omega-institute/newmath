import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OscillationRankFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OscillationRankFunctionUp : Type where
  | mk
      (source oscillation bound lineage derivativeStage rankComparison threshold transport
        replay provenance localName : BHist) :
      OscillationRankFunctionUp
  deriving DecidableEq

def oscillationRankFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oscillationRankFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oscillationRankFunctionEncodeBHist h

def oscillationRankFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oscillationRankFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oscillationRankFunctionDecodeBHist tail)

private theorem oscillationRankFunctionDecode_encode_bhist :
    ∀ h : BHist, oscillationRankFunctionDecodeBHist
      (oscillationRankFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oscillationRankFunctionFields : OscillationRankFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OscillationRankFunctionUp.mk source oscillation bound lineage derivativeStage
      rankComparison threshold transport replay provenance localName =>
      [source, oscillation, bound, lineage, derivativeStage, rankComparison, threshold,
        transport, replay, provenance, localName]

def oscillationRankFunctionToEventFlow : OscillationRankFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oscillationRankFunctionFields x).map oscillationRankFunctionEncodeBHist

private def oscillationRankFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => oscillationRankFunctionEventAt index rest

def oscillationRankFunctionFromEventFlow (ef : EventFlow) : Option OscillationRankFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OscillationRankFunctionUp.mk
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 0 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 1 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 2 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 3 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 4 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 5 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 6 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 7 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 8 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 9 ef))
      (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEventAt 10 ef)))

private theorem oscillationRankFunction_round_trip (x : OscillationRankFunctionUp) :
    oscillationRankFunctionFromEventFlow (oscillationRankFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source oscillation bound lineage derivativeStage rankComparison threshold transport
      replay provenance localName =>
      change
        some
          (OscillationRankFunctionUp.mk
            (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEncodeBHist source))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist oscillation))
            (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEncodeBHist bound))
            (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEncodeBHist lineage))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist derivativeStage))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist rankComparison))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist threshold))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist transport))
            (oscillationRankFunctionDecodeBHist (oscillationRankFunctionEncodeBHist replay))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist provenance))
            (oscillationRankFunctionDecodeBHist
              (oscillationRankFunctionEncodeBHist localName))) =
          some
            (OscillationRankFunctionUp.mk source oscillation bound lineage derivativeStage
              rankComparison threshold transport replay provenance localName)
      rw [oscillationRankFunctionDecode_encode_bhist source,
        oscillationRankFunctionDecode_encode_bhist oscillation,
        oscillationRankFunctionDecode_encode_bhist bound,
        oscillationRankFunctionDecode_encode_bhist lineage,
        oscillationRankFunctionDecode_encode_bhist derivativeStage,
        oscillationRankFunctionDecode_encode_bhist rankComparison,
        oscillationRankFunctionDecode_encode_bhist threshold,
        oscillationRankFunctionDecode_encode_bhist transport,
        oscillationRankFunctionDecode_encode_bhist replay,
        oscillationRankFunctionDecode_encode_bhist provenance,
        oscillationRankFunctionDecode_encode_bhist localName]

private theorem oscillationRankFunctionToEventFlow_injective
    {x y : OscillationRankFunctionUp} :
    oscillationRankFunctionToEventFlow x = oscillationRankFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oscillationRankFunctionFromEventFlow (oscillationRankFunctionToEventFlow x) =
        oscillationRankFunctionFromEventFlow (oscillationRankFunctionToEventFlow y) :=
    congrArg oscillationRankFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (oscillationRankFunction_round_trip x).symm
      (Eq.trans hread (oscillationRankFunction_round_trip y)))

instance oscillationRankFunctionBHistCarrier : BHistCarrier OscillationRankFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oscillationRankFunctionToEventFlow
  fromEventFlow := oscillationRankFunctionFromEventFlow

instance oscillationRankFunctionChapterTasteGate :
    ChapterTasteGate OscillationRankFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oscillationRankFunctionFromEventFlow
      (oscillationRankFunctionToEventFlow x) = some x
    exact oscillationRankFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (oscillationRankFunctionToEventFlow_injective heq)

theorem OscillationRankFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, oscillationRankFunctionDecodeBHist
        (oscillationRankFunctionEncodeBHist h) = h) ∧
      (∀ x : OscillationRankFunctionUp,
        oscillationRankFunctionFromEventFlow
          (oscillationRankFunctionToEventFlow x) = some x) ∧
        (∀ x y : OscillationRankFunctionUp,
          oscillationRankFunctionToEventFlow x = oscillationRankFunctionToEventFlow y →
            x = y) ∧
          oscillationRankFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨oscillationRankFunctionDecode_encode_bhist,
      oscillationRankFunction_round_trip,
      (fun _ _ heq => oscillationRankFunctionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OscillationRankFunctionUp

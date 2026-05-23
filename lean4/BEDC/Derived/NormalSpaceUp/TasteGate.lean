import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalSpaceUp : Type where
  | mk (topology closedLeft closedRight disjoint openLeft openRight transport replay
      provenance name : BHist) :
      NormalSpaceUp
  deriving DecidableEq

def normalSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalSpaceEncodeBHist h

def normalSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalSpaceDecodeBHist tail)

private theorem normalSpace_decode_encode_bhist :
    ∀ h : BHist, normalSpaceDecodeBHist (normalSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def normalSpaceFields : NormalSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalSpaceUp.mk topology closedLeft closedRight disjoint openLeft openRight transport
      replay provenance name =>
      [topology, closedLeft, closedRight, disjoint, openLeft, openRight, transport, replay,
        provenance, name]

def normalSpaceToEventFlow : NormalSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalSpaceFields x).map normalSpaceEncodeBHist

def normalSpaceFromEventFlow : EventFlow → Option NormalSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | topology :: closedLeft :: closedRight :: disjoint :: openLeft :: openRight :: transport ::
      replay :: provenance :: name :: [] =>
      some
        (NormalSpaceUp.mk
          (normalSpaceDecodeBHist topology)
          (normalSpaceDecodeBHist closedLeft)
          (normalSpaceDecodeBHist closedRight)
          (normalSpaceDecodeBHist disjoint)
          (normalSpaceDecodeBHist openLeft)
          (normalSpaceDecodeBHist openRight)
          (normalSpaceDecodeBHist transport)
          (normalSpaceDecodeBHist replay)
          (normalSpaceDecodeBHist provenance)
          (normalSpaceDecodeBHist name))
  | _ => none

private theorem normalSpace_round_trip :
    ∀ x : NormalSpaceUp, normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk topology closedLeft closedRight disjoint openLeft openRight transport replay provenance
      name =>
      change
        some
          (NormalSpaceUp.mk
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist topology))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist closedLeft))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist closedRight))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist disjoint))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist openLeft))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist openRight))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist transport))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist replay))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist provenance))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist name))) =
          some
            (NormalSpaceUp.mk topology closedLeft closedRight disjoint openLeft openRight
              transport replay provenance name)
      rw [normalSpace_decode_encode_bhist topology,
        normalSpace_decode_encode_bhist closedLeft,
        normalSpace_decode_encode_bhist closedRight,
        normalSpace_decode_encode_bhist disjoint,
        normalSpace_decode_encode_bhist openLeft,
        normalSpace_decode_encode_bhist openRight,
        normalSpace_decode_encode_bhist transport,
        normalSpace_decode_encode_bhist replay,
        normalSpace_decode_encode_bhist provenance,
        normalSpace_decode_encode_bhist name]

private theorem normalSpaceToEventFlow_injective {x y : NormalSpaceUp} :
    normalSpaceToEventFlow x = normalSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalSpaceFromEventFlow (normalSpaceToEventFlow x) =
        normalSpaceFromEventFlow (normalSpaceToEventFlow y) :=
    congrArg normalSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (normalSpace_round_trip x).symm
      (Eq.trans hread (normalSpace_round_trip y)))

instance normalSpaceBHistCarrier : BHistCarrier NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalSpaceToEventFlow
  fromEventFlow := normalSpaceFromEventFlow

instance normalSpaceChapterTasteGate : ChapterTasteGate NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x
    exact normalSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (normalSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NormalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalSpaceChapterTasteGate

end BEDC.Derived.NormalSpaceUp

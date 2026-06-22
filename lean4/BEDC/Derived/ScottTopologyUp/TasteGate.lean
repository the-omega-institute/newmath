import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScottTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScottTopologyUp : Type where
  | mk (D S U I B O H C P N : BHist) : ScottTopologyUp
  deriving DecidableEq

def ScottTopologyTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ScottTopologyTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ScottTopologyTasteGate_single_carrier_alignment_encodeBHist h

def ScottTopologyTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem scottTopology_decode_encode_bhist :
    forall h : BHist,
      ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
        (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ScottTopologyTasteGate_single_carrier_alignment_toEventFlow :
    ScottTopologyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ScottTopologyUp.mk D S U I B O H C P N =>
      [[BMark.b0],
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist D,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist S,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist U,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist I,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist B,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist O,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist H,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist C,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist P,
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist N]

def ScottTopologyTasteGate_single_carrier_alignment_fields :
    ScottTopologyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScottTopologyUp.mk D S U I B O H C P N => [D, S, U, I, B, O, H, C, P, N]

def ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option ScottTopologyUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: D :: S :: U :: I :: B :: O :: H :: C :: P :: N :: [] =>
      some
        (ScottTopologyUp.mk
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist D)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist S)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist U)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist I)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist B)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist O)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist H)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist C)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist P)
          (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem scottTopology_round_trip :
    forall x : ScottTopologyUp,
      ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow
        (ScottTopologyTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S U I B O H C P N =>
      change
        some
          (ScottTopologyUp.mk
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist D))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist S))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist U))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist I))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist B))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist O))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist H))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist C))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist P))
            (ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
              (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ScottTopologyUp.mk D S U I B O H C P N)
      rw [scottTopology_decode_encode_bhist D,
        scottTopology_decode_encode_bhist S,
        scottTopology_decode_encode_bhist U,
        scottTopology_decode_encode_bhist I,
        scottTopology_decode_encode_bhist B,
        scottTopology_decode_encode_bhist O,
        scottTopology_decode_encode_bhist H,
        scottTopology_decode_encode_bhist C,
        scottTopology_decode_encode_bhist P,
        scottTopology_decode_encode_bhist N]

private theorem scottTopology_toEventFlow_injective {x y : ScottTopologyUp} :
    ScottTopologyTasteGate_single_carrier_alignment_toEventFlow x =
      ScottTopologyTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow
          (ScottTopologyTasteGate_single_carrier_alignment_toEventFlow x) =
        ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow
          (ScottTopologyTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (scottTopology_round_trip x).symm
      (Eq.trans hread (scottTopology_round_trip y)))

instance scottTopologyBHistCarrier : BHistCarrier ScottTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ScottTopologyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow

instance scottTopologyChapterTasteGate : ChapterTasteGate ScottTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ScottTopologyTasteGate_single_carrier_alignment_fromEventFlow
        (ScottTopologyTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact scottTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (scottTopology_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ScottTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scottTopologyChapterTasteGate

theorem ScottTopologyTasteGate_single_carrier_alignment :
    (forall D S U I B O H C P N : BHist,
      ScottTopologyTasteGate_single_carrier_alignment_fields
          (ScottTopologyUp.mk D S U I B O H C P N) =
        [D, S, U, I, B, O, H, C, P, N]) ∧
      (forall h : BHist,
        ScottTopologyTasteGate_single_carrier_alignment_decodeBHist
          (ScottTopologyTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        ScottTopologyTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨(by intros; rfl), scottTopology_decode_encode_bhist, rfl⟩

end BEDC.Derived.ScottTopologyUp

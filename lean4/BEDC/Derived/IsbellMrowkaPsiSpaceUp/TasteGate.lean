import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsbellMrowkaPsiSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IsbellMrowkaPsiSpaceUp : Type where
  | mk (N A T I F O S W H C P L : BHist) : IsbellMrowkaPsiSpaceUp
  deriving DecidableEq

def isbellMrowkaPsiSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isbellMrowkaPsiSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isbellMrowkaPsiSpaceEncodeBHist h

def isbellMrowkaPsiSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isbellMrowkaPsiSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isbellMrowkaPsiSpaceDecodeBHist tail)

private theorem isbellMrowkaPsiSpace_decode_encode_bhist :
    ∀ h : BHist, isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def isbellMrowkaPsiSpaceFields : IsbellMrowkaPsiSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IsbellMrowkaPsiSpaceUp.mk N A T I F O S W H C P L => [N, A, T, I, F, O, S, W, H, C, P, L]

def isbellMrowkaPsiSpaceToEventFlow : IsbellMrowkaPsiSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map isbellMrowkaPsiSpaceEncodeBHist (isbellMrowkaPsiSpaceFields x)

def isbellMrowkaPsiSpaceFromEventFlow : EventFlow → Option IsbellMrowkaPsiSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | N :: A :: T :: I :: F :: O :: S :: W :: H :: C :: P :: L :: [] =>
      some
        (IsbellMrowkaPsiSpaceUp.mk
          (isbellMrowkaPsiSpaceDecodeBHist N)
          (isbellMrowkaPsiSpaceDecodeBHist A)
          (isbellMrowkaPsiSpaceDecodeBHist T)
          (isbellMrowkaPsiSpaceDecodeBHist I)
          (isbellMrowkaPsiSpaceDecodeBHist F)
          (isbellMrowkaPsiSpaceDecodeBHist O)
          (isbellMrowkaPsiSpaceDecodeBHist S)
          (isbellMrowkaPsiSpaceDecodeBHist W)
          (isbellMrowkaPsiSpaceDecodeBHist H)
          (isbellMrowkaPsiSpaceDecodeBHist C)
          (isbellMrowkaPsiSpaceDecodeBHist P)
          (isbellMrowkaPsiSpaceDecodeBHist L))
  | _ => none

private theorem isbellMrowkaPsiSpace_round_trip :
    ∀ x : IsbellMrowkaPsiSpaceUp,
      isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N A T I F O S W H C P L =>
      change
        some
          (IsbellMrowkaPsiSpaceUp.mk
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist N))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist A))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist T))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist I))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist F))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist O))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist S))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist W))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist H))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist C))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist P))
            (isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist L))) =
          some (IsbellMrowkaPsiSpaceUp.mk N A T I F O S W H C P L)
      rw [isbellMrowkaPsiSpace_decode_encode_bhist N,
        isbellMrowkaPsiSpace_decode_encode_bhist A,
        isbellMrowkaPsiSpace_decode_encode_bhist T,
        isbellMrowkaPsiSpace_decode_encode_bhist I,
        isbellMrowkaPsiSpace_decode_encode_bhist F,
        isbellMrowkaPsiSpace_decode_encode_bhist O,
        isbellMrowkaPsiSpace_decode_encode_bhist S,
        isbellMrowkaPsiSpace_decode_encode_bhist W,
        isbellMrowkaPsiSpace_decode_encode_bhist H,
        isbellMrowkaPsiSpace_decode_encode_bhist C,
        isbellMrowkaPsiSpace_decode_encode_bhist P,
        isbellMrowkaPsiSpace_decode_encode_bhist L]

private theorem isbellMrowkaPsiSpaceToEventFlow_injective
    {x y : IsbellMrowkaPsiSpaceUp} :
    isbellMrowkaPsiSpaceToEventFlow x = isbellMrowkaPsiSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) =
        isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow y) :=
    congrArg isbellMrowkaPsiSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (isbellMrowkaPsiSpace_round_trip x).symm
      (Eq.trans hread (isbellMrowkaPsiSpace_round_trip y)))

instance isbellMrowkaPsiSpaceBHistCarrier : BHistCarrier IsbellMrowkaPsiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isbellMrowkaPsiSpaceToEventFlow
  fromEventFlow := isbellMrowkaPsiSpaceFromEventFlow

instance isbellMrowkaPsiSpaceChapterTasteGate : ChapterTasteGate IsbellMrowkaPsiSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change isbellMrowkaPsiSpaceFromEventFlow (isbellMrowkaPsiSpaceToEventFlow x) = some x
    exact isbellMrowkaPsiSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (isbellMrowkaPsiSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate IsbellMrowkaPsiSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isbellMrowkaPsiSpaceChapterTasteGate

theorem IsbellMrowkaPsiSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist h) = h) ∧
      isbellMrowkaPsiSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have decodeEncode :
      ∀ h : BHist, isbellMrowkaPsiSpaceDecodeBHist (isbellMrowkaPsiSpaceEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · exact decodeEncode
  · rfl

end BEDC.Derived.IsbellMrowkaPsiSpaceUp

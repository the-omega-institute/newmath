import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyDisconnectedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyDisconnectedSpaceUp : Type where
  | mk (O K Hd x y U V L Z R C P N : BHist) : TotallyDisconnectedSpaceUp
  deriving DecidableEq

def totallyDisconnectedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyDisconnectedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyDisconnectedSpaceEncodeBHist h

def totallyDisconnectedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyDisconnectedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyDisconnectedSpaceDecodeBHist tail)

private theorem TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totallyDisconnectedSpaceToEventFlow : TotallyDisconnectedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyDisconnectedSpaceUp.mk O K Hd x y U V L Z R C P N =>
      [totallyDisconnectedSpaceEncodeBHist O,
        totallyDisconnectedSpaceEncodeBHist K,
        totallyDisconnectedSpaceEncodeBHist Hd,
        totallyDisconnectedSpaceEncodeBHist x,
        totallyDisconnectedSpaceEncodeBHist y,
        totallyDisconnectedSpaceEncodeBHist U,
        totallyDisconnectedSpaceEncodeBHist V,
        totallyDisconnectedSpaceEncodeBHist L,
        totallyDisconnectedSpaceEncodeBHist Z,
        totallyDisconnectedSpaceEncodeBHist R,
        totallyDisconnectedSpaceEncodeBHist C,
        totallyDisconnectedSpaceEncodeBHist P,
        totallyDisconnectedSpaceEncodeBHist N]

def totallyDisconnectedSpaceFromEventFlow : EventFlow → Option TotallyDisconnectedSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | O :: K :: Hd :: x :: y :: U :: V :: L :: Z :: R :: C :: P :: N :: [] =>
      some
        (TotallyDisconnectedSpaceUp.mk
          (totallyDisconnectedSpaceDecodeBHist O)
          (totallyDisconnectedSpaceDecodeBHist K)
          (totallyDisconnectedSpaceDecodeBHist Hd)
          (totallyDisconnectedSpaceDecodeBHist x)
          (totallyDisconnectedSpaceDecodeBHist y)
          (totallyDisconnectedSpaceDecodeBHist U)
          (totallyDisconnectedSpaceDecodeBHist V)
          (totallyDisconnectedSpaceDecodeBHist L)
          (totallyDisconnectedSpaceDecodeBHist Z)
          (totallyDisconnectedSpaceDecodeBHist R)
          (totallyDisconnectedSpaceDecodeBHist C)
          (totallyDisconnectedSpaceDecodeBHist P)
          (totallyDisconnectedSpaceDecodeBHist N))
  | _ => none

private theorem TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TotallyDisconnectedSpaceUp,
      totallyDisconnectedSpaceFromEventFlow (totallyDisconnectedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk O K Hd x y U V L Z R C P N =>
      change
        some
          (TotallyDisconnectedSpaceUp.mk
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist O))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist K))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist Hd))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist x))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist y))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist U))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist V))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist L))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist Z))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist R))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist C))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist P))
            (totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist N))) =
          some (TotallyDisconnectedSpaceUp.mk O K Hd x y U V L Z R C P N)
      rw [TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode O,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode K,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode Hd,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode x,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode y,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode U,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode V,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode L,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode Z,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode R,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode C,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode P,
        TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TotallyDisconnectedSpaceUp} :
    totallyDisconnectedSpaceToEventFlow x = totallyDisconnectedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyDisconnectedSpaceFromEventFlow (totallyDisconnectedSpaceToEventFlow x) =
        totallyDisconnectedSpaceFromEventFlow (totallyDisconnectedSpaceToEventFlow y) :=
    congrArg totallyDisconnectedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance totallyDisconnectedSpaceBHistCarrier : BHistCarrier TotallyDisconnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyDisconnectedSpaceToEventFlow
  fromEventFlow := totallyDisconnectedSpaceFromEventFlow

instance totallyDisconnectedSpaceChapterTasteGate : ChapterTasteGate TotallyDisconnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totallyDisconnectedSpaceFromEventFlow (totallyDisconnectedSpaceToEventFlow x) = some x
    exact TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem TotallyDisconnectedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, totallyDisconnectedSpaceDecodeBHist (totallyDisconnectedSpaceEncodeBHist h) = h) ∧
      totallyDisconnectedSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨TotallyDisconnectedSpaceTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.TotallyDisconnectedSpaceUp

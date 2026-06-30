import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FarEndDiagramUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FarEndDiagramUp : Type where
  | mk (R G K C L S F A H T P N : BHist) : FarEndDiagramUp
  deriving DecidableEq

def farEndDiagramEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: farEndDiagramEncodeBHist h
  | BHist.e1 h => BMark.b1 :: farEndDiagramEncodeBHist h

def farEndDiagramDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (farEndDiagramDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (farEndDiagramDecodeBHist tail)

theorem FarEndDiagramTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, farEndDiagramDecodeBHist (farEndDiagramEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def farEndDiagramFields : FarEndDiagramUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FarEndDiagramUp.mk R G K C L S F A H T P N => [R, G, K, C, L, S, F, A, H, T, P, N]

def farEndDiagramToEventFlow : FarEndDiagramUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (farEndDiagramFields x).map farEndDiagramEncodeBHist

def farEndDiagramFromEventFlow : EventFlow → Option FarEndDiagramUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | R :: G :: K :: C :: L :: S :: F :: A :: H :: T :: P :: N :: [] =>
      some
        (FarEndDiagramUp.mk
          (farEndDiagramDecodeBHist R)
          (farEndDiagramDecodeBHist G)
          (farEndDiagramDecodeBHist K)
          (farEndDiagramDecodeBHist C)
          (farEndDiagramDecodeBHist L)
          (farEndDiagramDecodeBHist S)
          (farEndDiagramDecodeBHist F)
          (farEndDiagramDecodeBHist A)
          (farEndDiagramDecodeBHist H)
          (farEndDiagramDecodeBHist T)
          (farEndDiagramDecodeBHist P)
          (farEndDiagramDecodeBHist N))
  | _ => none

private theorem FarEndDiagramTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FarEndDiagramUp,
      farEndDiagramFromEventFlow (farEndDiagramToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R G K C L S F A H T P N =>
      change
        some
          (FarEndDiagramUp.mk
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist R))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist G))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist K))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist C))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist L))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist S))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist F))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist A))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist H))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist T))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist P))
            (farEndDiagramDecodeBHist (farEndDiagramEncodeBHist N))) =
          some (FarEndDiagramUp.mk R G K C L S F A H T P N)
      rw [FarEndDiagramTasteGate_single_carrier_alignment_decode_encode R,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode G,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode K,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode C,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode L,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode S,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode F,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode A,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode H,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode T,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode P,
        FarEndDiagramTasteGate_single_carrier_alignment_decode_encode N]

private theorem FarEndDiagramTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : FarEndDiagramUp} :
    farEndDiagramToEventFlow x = farEndDiagramToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = farEndDiagramFromEventFlow (farEndDiagramToEventFlow x) :=
        (FarEndDiagramTasteGate_single_carrier_alignment_round_trip x).symm
      _ = farEndDiagramFromEventFlow (farEndDiagramToEventFlow y) :=
        congrArg farEndDiagramFromEventFlow hxy
      _ = some y :=
        FarEndDiagramTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance FarEndDiagramTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FarEndDiagramUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := farEndDiagramToEventFlow
  fromEventFlow := farEndDiagramFromEventFlow

instance FarEndDiagramTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FarEndDiagramUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change farEndDiagramFromEventFlow (farEndDiagramToEventFlow x) = some x
    exact FarEndDiagramTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FarEndDiagramTasteGate_single_carrier_alignment_ToEventFlow_injective heq)

theorem FarEndDiagramTasteGate_single_carrier_alignment :
    (∀ h : BHist, farEndDiagramDecodeBHist (farEndDiagramEncodeBHist h) = h) ∧
      farEndDiagramFields
          (FarEndDiagramUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        farEndDiagramEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FarEndDiagramTasteGate_single_carrier_alignment_decode_encode,
      rfl,
      rfl⟩

end BEDC.Derived.FarEndDiagramUp

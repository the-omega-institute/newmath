import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardyCesaroMeanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardyCesaroMeanUp : Type where
  | mk (S P U D R E T C Q N : BHist) : HardyCesaroMeanUp

def hardyCesaroMeanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardyCesaroMeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardyCesaroMeanEncodeBHist h

def hardyCesaroMeanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardyCesaroMeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardyCesaroMeanDecodeBHist tail)

private theorem hardyCesaroMean_decode_encode_bhist :
    ∀ h : BHist, hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hardyCesaroMeanFields : HardyCesaroMeanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardyCesaroMeanUp.mk S P U D R E T C Q N => [S, P, U, D, R, E, T, C, Q, N]

def hardyCesaroMeanToEventFlow : HardyCesaroMeanUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HardyCesaroMeanUp.mk S P U D R E T C Q N =>
      [hardyCesaroMeanEncodeBHist S,
        hardyCesaroMeanEncodeBHist P,
        hardyCesaroMeanEncodeBHist U,
        hardyCesaroMeanEncodeBHist D,
        hardyCesaroMeanEncodeBHist R,
        hardyCesaroMeanEncodeBHist E,
        hardyCesaroMeanEncodeBHist T,
        hardyCesaroMeanEncodeBHist C,
        hardyCesaroMeanEncodeBHist Q,
        hardyCesaroMeanEncodeBHist N]

def hardyCesaroMeanFromEventFlow : EventFlow → Option HardyCesaroMeanUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: P :: U :: D :: R :: E :: T :: C :: Q :: N :: [] =>
      some
        (HardyCesaroMeanUp.mk
          (hardyCesaroMeanDecodeBHist S)
          (hardyCesaroMeanDecodeBHist P)
          (hardyCesaroMeanDecodeBHist U)
          (hardyCesaroMeanDecodeBHist D)
          (hardyCesaroMeanDecodeBHist R)
          (hardyCesaroMeanDecodeBHist E)
          (hardyCesaroMeanDecodeBHist T)
          (hardyCesaroMeanDecodeBHist C)
          (hardyCesaroMeanDecodeBHist Q)
          (hardyCesaroMeanDecodeBHist N))
  | _ => none

private theorem hardyCesaroMean_round_trip :
    ∀ x : HardyCesaroMeanUp,
      hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S P U D R E T C Q N =>
      change
        some
            (HardyCesaroMeanUp.mk
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist S))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist P))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist U))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist D))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist R))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist E))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist T))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist C))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist Q))
              (hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist N))) =
          some (HardyCesaroMeanUp.mk S P U D R E T C Q N)
      rw [hardyCesaroMean_decode_encode_bhist S,
        hardyCesaroMean_decode_encode_bhist P,
        hardyCesaroMean_decode_encode_bhist U,
        hardyCesaroMean_decode_encode_bhist D,
        hardyCesaroMean_decode_encode_bhist R,
        hardyCesaroMean_decode_encode_bhist E,
        hardyCesaroMean_decode_encode_bhist T,
        hardyCesaroMean_decode_encode_bhist C,
        hardyCesaroMean_decode_encode_bhist Q,
        hardyCesaroMean_decode_encode_bhist N]

private theorem hardyCesaroMeanToEventFlow_injective
    {x y : HardyCesaroMeanUp} :
    hardyCesaroMeanToEventFlow x = hardyCesaroMeanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) =
        hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow y) :=
    congrArg hardyCesaroMeanFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (hardyCesaroMean_round_trip x).symm
      (Eq.trans hread (hardyCesaroMean_round_trip y)))

private theorem hardyCesaroMean_fields_faithful :
    ∀ x y : HardyCesaroMeanUp, hardyCesaroMeanFields x = hardyCesaroMeanFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S P U D R E T C Q N =>
      cases y with
      | mk S' P' U' D' R' E' T' C' Q' N' =>
          cases hfields
          rfl

instance hardyCesaroMeanBHistCarrier : BHistCarrier HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardyCesaroMeanToEventFlow
  fromEventFlow := hardyCesaroMeanFromEventFlow

instance hardyCesaroMeanChapterTasteGate : ChapterTasteGate HardyCesaroMeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardyCesaroMeanFromEventFlow (hardyCesaroMeanToEventFlow x) = some x
    exact hardyCesaroMean_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hardyCesaroMeanToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HardyCesaroMeanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hardyCesaroMeanChapterTasteGate

theorem HardyCesaroMeanTasteGate_single_carrier_alignment :
    (∀ h : BHist, hardyCesaroMeanDecodeBHist (hardyCesaroMeanEncodeBHist h) = h) ∧
      hardyCesaroMeanFields
          (HardyCesaroMeanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        hardyCesaroMeanEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨hardyCesaroMean_decode_encode_bhist,
      rfl,
      rfl⟩

end BEDC.Derived.HardyCesaroMeanUp

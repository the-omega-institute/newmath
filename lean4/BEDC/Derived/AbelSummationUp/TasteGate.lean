import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelSummationUp : Type where
  | mk (S A D B T R E H C P N : BHist) : AbelSummationUp

def abelSummationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelSummationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelSummationEncodeBHist h

def abelSummationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelSummationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelSummationDecodeBHist tail)

private theorem abelSummation_decode_encode_bhist :
    ∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abelSummationFields : AbelSummationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummationUp.mk S A D B T R E H C P N => [S, A, D, B, T, R, E, H, C, P, N]

def abelSummationToEventFlow : AbelSummationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AbelSummationUp.mk S A D B T R E H C P N =>
      [abelSummationEncodeBHist S,
        abelSummationEncodeBHist A,
        abelSummationEncodeBHist D,
        abelSummationEncodeBHist B,
        abelSummationEncodeBHist T,
        abelSummationEncodeBHist R,
        abelSummationEncodeBHist E,
        abelSummationEncodeBHist H,
        abelSummationEncodeBHist C,
        abelSummationEncodeBHist P,
        abelSummationEncodeBHist N]

def abelSummationFromEventFlow : EventFlow → Option AbelSummationUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: A :: D :: B :: T :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (AbelSummationUp.mk
          (abelSummationDecodeBHist S)
          (abelSummationDecodeBHist A)
          (abelSummationDecodeBHist D)
          (abelSummationDecodeBHist B)
          (abelSummationDecodeBHist T)
          (abelSummationDecodeBHist R)
          (abelSummationDecodeBHist E)
          (abelSummationDecodeBHist H)
          (abelSummationDecodeBHist C)
          (abelSummationDecodeBHist P)
          (abelSummationDecodeBHist N))
  | _ => none

private theorem abelSummation_round_trip :
    ∀ x : AbelSummationUp,
      abelSummationFromEventFlow (abelSummationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A D B T R E H C P N =>
      change
        some
            (AbelSummationUp.mk
              (abelSummationDecodeBHist (abelSummationEncodeBHist S))
              (abelSummationDecodeBHist (abelSummationEncodeBHist A))
              (abelSummationDecodeBHist (abelSummationEncodeBHist D))
              (abelSummationDecodeBHist (abelSummationEncodeBHist B))
              (abelSummationDecodeBHist (abelSummationEncodeBHist T))
              (abelSummationDecodeBHist (abelSummationEncodeBHist R))
              (abelSummationDecodeBHist (abelSummationEncodeBHist E))
              (abelSummationDecodeBHist (abelSummationEncodeBHist H))
              (abelSummationDecodeBHist (abelSummationEncodeBHist C))
              (abelSummationDecodeBHist (abelSummationEncodeBHist P))
              (abelSummationDecodeBHist (abelSummationEncodeBHist N))) =
          some (AbelSummationUp.mk S A D B T R E H C P N)
      rw [abelSummation_decode_encode_bhist S,
        abelSummation_decode_encode_bhist A,
        abelSummation_decode_encode_bhist D,
        abelSummation_decode_encode_bhist B,
        abelSummation_decode_encode_bhist T,
        abelSummation_decode_encode_bhist R,
        abelSummation_decode_encode_bhist E,
        abelSummation_decode_encode_bhist H,
        abelSummation_decode_encode_bhist C,
        abelSummation_decode_encode_bhist P,
        abelSummation_decode_encode_bhist N]

private theorem abelSummationToEventFlow_injective
    {x y : AbelSummationUp} :
    abelSummationToEventFlow x = abelSummationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      abelSummationFromEventFlow (abelSummationToEventFlow x) =
        abelSummationFromEventFlow (abelSummationToEventFlow y) :=
    congrArg abelSummationFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (abelSummation_round_trip x).symm
      (Eq.trans hread (abelSummation_round_trip y)))

private theorem abelSummation_fields_faithful :
    ∀ x y : AbelSummationUp, abelSummationFields x = abelSummationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S A D B T R E H C P N =>
      cases y with
      | mk S' A' D' B' T' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance abelSummationBHistCarrier : BHistCarrier AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelSummationToEventFlow
  fromEventFlow := abelSummationFromEventFlow

instance abelSummationChapterTasteGate : ChapterTasteGate AbelSummationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelSummationFromEventFlow (abelSummationToEventFlow x) = some x
    exact abelSummation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (abelSummationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AbelSummationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelSummationChapterTasteGate

theorem AbelSummationTasteGate_single_carrier_alignment :
    (∀ h : BHist, abelSummationDecodeBHist (abelSummationEncodeBHist h) = h) ∧
      abelSummationFields
          (AbelSummationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        abelSummationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨abelSummation_decode_encode_bhist,
      rfl,
      rfl⟩

end BEDC.Derived.AbelSummationUp

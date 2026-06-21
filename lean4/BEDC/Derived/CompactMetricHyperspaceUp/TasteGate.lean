import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricHyperspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricHyperspaceUp : Type where
  | mk (X H F D V L T C P N : BHist) : CompactMetricHyperspaceUp

def compactMetricHyperspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricHyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricHyperspaceEncodeBHist h

def compactMetricHyperspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricHyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricHyperspaceDecodeBHist tail)

private theorem compactMetricHyperspaceDecode_encode_bhist :
    ∀ h : BHist,
      compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricHyperspaceFields : CompactMetricHyperspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricHyperspaceUp.mk X H F D V L T C P N => [X, H, F, D, V, L, T, C, P, N]

def compactMetricHyperspaceToEventFlow : CompactMetricHyperspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactMetricHyperspaceFields x).map compactMetricHyperspaceEncodeBHist

def compactMetricHyperspaceFromEventFlow : EventFlow → Option CompactMetricHyperspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: H :: F :: D :: V :: L :: T :: C :: P :: N :: [] =>
      some
        (CompactMetricHyperspaceUp.mk
          (compactMetricHyperspaceDecodeBHist X)
          (compactMetricHyperspaceDecodeBHist H)
          (compactMetricHyperspaceDecodeBHist F)
          (compactMetricHyperspaceDecodeBHist D)
          (compactMetricHyperspaceDecodeBHist V)
          (compactMetricHyperspaceDecodeBHist L)
          (compactMetricHyperspaceDecodeBHist T)
          (compactMetricHyperspaceDecodeBHist C)
          (compactMetricHyperspaceDecodeBHist P)
          (compactMetricHyperspaceDecodeBHist N))
  | _ => none

private theorem compactMetricHyperspace_round_trip :
    ∀ x : CompactMetricHyperspaceUp,
      compactMetricHyperspaceFromEventFlow (compactMetricHyperspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X H F D V L T C P N =>
      change
        some
          (CompactMetricHyperspaceUp.mk
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist X))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist H))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist F))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist D))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist V))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist L))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist T))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist C))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist P))
            (compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist N))) =
          some (CompactMetricHyperspaceUp.mk X H F D V L T C P N)
      rw [compactMetricHyperspaceDecode_encode_bhist X,
        compactMetricHyperspaceDecode_encode_bhist H,
        compactMetricHyperspaceDecode_encode_bhist F,
        compactMetricHyperspaceDecode_encode_bhist D,
        compactMetricHyperspaceDecode_encode_bhist V,
        compactMetricHyperspaceDecode_encode_bhist L,
        compactMetricHyperspaceDecode_encode_bhist T,
        compactMetricHyperspaceDecode_encode_bhist C,
        compactMetricHyperspaceDecode_encode_bhist P,
        compactMetricHyperspaceDecode_encode_bhist N]

private theorem compactMetricHyperspaceToEventFlow_injective
    {x y : CompactMetricHyperspaceUp} :
    compactMetricHyperspaceToEventFlow x = compactMetricHyperspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricHyperspaceFromEventFlow (compactMetricHyperspaceToEventFlow x) =
        compactMetricHyperspaceFromEventFlow (compactMetricHyperspaceToEventFlow y) :=
    congrArg compactMetricHyperspaceFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (compactMetricHyperspace_round_trip x).symm
        (Eq.trans hread (compactMetricHyperspace_round_trip y)))

private theorem compactMetricHyperspace_fields_faithful :
    ∀ x y : CompactMetricHyperspaceUp,
      compactMetricHyperspaceFields x = compactMetricHyperspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 H1 F1 D1 V1 L1 T1 C1 P1 N1 =>
      cases y with
      | mk X2 H2 F2 D2 V2 L2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactMetricHyperspaceBHistCarrier :
    BHistCarrier CompactMetricHyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricHyperspaceToEventFlow
  fromEventFlow := compactMetricHyperspaceFromEventFlow

instance compactMetricHyperspaceChapterTasteGate :
    ChapterTasteGate CompactMetricHyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactMetricHyperspaceFromEventFlow
        (compactMetricHyperspaceToEventFlow x) = some x
    exact compactMetricHyperspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactMetricHyperspaceToEventFlow_injective heq)

instance compactMetricHyperspaceFieldFaithful :
    FieldFaithful CompactMetricHyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactMetricHyperspaceFields
  field_faithful := compactMetricHyperspace_fields_faithful

theorem CompactMetricHyperspaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactMetricHyperspaceDecodeBHist (compactMetricHyperspaceEncodeBHist h) = h) ∧
      (∀ x y : CompactMetricHyperspaceUp,
        compactMetricHyperspaceFields x = compactMetricHyperspaceFields y → x = y) ∧
        compactMetricHyperspaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨compactMetricHyperspaceDecode_encode_bhist,
      compactMetricHyperspace_fields_faithful,
      rfl⟩

end BEDC.Derived.CompactMetricHyperspaceUp

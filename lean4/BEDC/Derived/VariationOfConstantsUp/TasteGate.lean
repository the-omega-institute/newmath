import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationOfConstantsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationOfConstantsUp : Type where
  | mk (O P L G R H C Q N : BHist) : VariationOfConstantsUp
  deriving DecidableEq

def variationOfConstantsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationOfConstantsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationOfConstantsEncodeBHist h

def variationOfConstantsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationOfConstantsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationOfConstantsDecodeBHist tail)

private theorem VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationOfConstantsToEventFlow : VariationOfConstantsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | VariationOfConstantsUp.mk O P L G R H C Q N =>
      [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
        variationOfConstantsEncodeBHist O,
        variationOfConstantsEncodeBHist P,
        variationOfConstantsEncodeBHist L,
        variationOfConstantsEncodeBHist G,
        variationOfConstantsEncodeBHist R,
        variationOfConstantsEncodeBHist H,
        variationOfConstantsEncodeBHist C,
        variationOfConstantsEncodeBHist Q,
        variationOfConstantsEncodeBHist N]

def variationOfConstantsFromEventFlow : EventFlow → Option VariationOfConstantsUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restO =>
      match restO with
      | [] => none
      | O :: restP =>
          match restP with
          | [] => none
          | P :: restL =>
              match restL with
              | [] => none
              | L :: restG =>
                  match restG with
                  | [] => none
                  | G :: restR =>
                      match restR with
                      | [] => none
                      | R :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restQ =>
                                  match restQ with
                                  | [] => none
                                  | Q :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (VariationOfConstantsUp.mk
                                                  (variationOfConstantsDecodeBHist O)
                                                  (variationOfConstantsDecodeBHist P)
                                                  (variationOfConstantsDecodeBHist L)
                                                  (variationOfConstantsDecodeBHist G)
                                                  (variationOfConstantsDecodeBHist R)
                                                  (variationOfConstantsDecodeBHist H)
                                                  (variationOfConstantsDecodeBHist C)
                                                  (variationOfConstantsDecodeBHist Q)
                                                  (variationOfConstantsDecodeBHist N))
                                          | _ :: _ => none

private theorem VariationOfConstantsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : VariationOfConstantsUp,
      variationOfConstantsFromEventFlow (variationOfConstantsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O P L G R H C Q N =>
      change
        some
          (VariationOfConstantsUp.mk
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist O))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist P))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist L))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist G))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist R))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist H))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist C))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist Q))
            (variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist N))) =
          some (VariationOfConstantsUp.mk O P L G R H C Q N)
      rw [VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode O,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode P,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode L,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode G,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode R,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode H,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode C,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode Q,
        VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode N]

private theorem VariationOfConstantsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VariationOfConstantsUp} :
    variationOfConstantsToEventFlow x = variationOfConstantsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationOfConstantsFromEventFlow (variationOfConstantsToEventFlow x) =
        variationOfConstantsFromEventFlow (variationOfConstantsToEventFlow y) :=
    congrArg variationOfConstantsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VariationOfConstantsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VariationOfConstantsTasteGate_single_carrier_alignment_round_trip y)))

instance variationOfConstantsBHistCarrier : BHistCarrier VariationOfConstantsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationOfConstantsToEventFlow
  fromEventFlow := variationOfConstantsFromEventFlow

instance variationOfConstantsChapterTasteGate : ChapterTasteGate VariationOfConstantsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationOfConstantsFromEventFlow (variationOfConstantsToEventFlow x) = some x
    exact VariationOfConstantsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VariationOfConstantsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem VariationOfConstantsTasteGate_single_carrier_alignment :
    (∀ h : BHist, variationOfConstantsDecodeBHist (variationOfConstantsEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VariationOfConstantsUp) ∧
        Nonempty (ChapterTasteGate VariationOfConstantsUp) ∧
          variationOfConstantsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨VariationOfConstantsTasteGate_single_carrier_alignment_decode_encode,
      ⟨variationOfConstantsBHistCarrier⟩,
      ⟨variationOfConstantsChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.VariationOfConstantsUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedMeshModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedMeshModulusUp : Type where
  | mk (F G T I H C P N : BHist) : RegulatedMeshModulusUp
  deriving DecidableEq

def regulatedMeshModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedMeshModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedMeshModulusEncodeBHist h

def regulatedMeshModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedMeshModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedMeshModulusDecodeBHist tail)

private theorem RegulatedMeshModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedMeshModulusToEventFlow : RegulatedMeshModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedMeshModulusUp.mk F G T I H C P N =>
      [[BMark.b0],
        regulatedMeshModulusEncodeBHist F,
        [BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeshModulusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regulatedMeshModulusEncodeBHist N]

def regulatedMeshModulusFromEventFlow : EventFlow → Option RegulatedMeshModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagF :: restF =>
      match restF with
      | [] => none
      | F :: restGTag =>
          match restGTag with
          | [] => none
          | _tagG :: restG =>
              match restG with
              | [] => none
              | G :: restTTag =>
                  match restTTag with
                  | [] => none
                  | _tagT :: restT =>
                      match restT with
                      | [] => none
                      | T :: restITag =>
                          match restITag with
                          | [] => none
                          | _tagI :: restI =>
                              match restI with
                              | [] => none
                              | I :: restHTag =>
                                  match restHTag with
                                  | [] => none
                                  | _tagH :: restH =>
                                      match restH with
                                      | [] => none
                                      | H :: restCTag =>
                                          match restCTag with
                                          | [] => none
                                          | _tagC :: restC =>
                                              match restC with
                                              | [] => none
                                              | C :: restPTag =>
                                                  match restPTag with
                                                  | [] => none
                                                  | _tagP :: restP =>
                                                      match restP with
                                                      | [] => none
                                                      | P :: restNTag =>
                                                          match restNTag with
                                                          | [] => none
                                                          | _tagN :: restN =>
                                                              match restN with
                                                              | [] => none
                                                              | N :: rest =>
                                                                  match rest with
                                                                  | [] =>
                                                                      some
                                                                        (RegulatedMeshModulusUp.mk
                                                                          (regulatedMeshModulusDecodeBHist F)
                                                                          (regulatedMeshModulusDecodeBHist G)
                                                                          (regulatedMeshModulusDecodeBHist T)
                                                                          (regulatedMeshModulusDecodeBHist I)
                                                                          (regulatedMeshModulusDecodeBHist H)
                                                                          (regulatedMeshModulusDecodeBHist C)
                                                                          (regulatedMeshModulusDecodeBHist P)
                                                                          (regulatedMeshModulusDecodeBHist N))
                                                                  | _ :: _ => none

private theorem RegulatedMeshModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatedMeshModulusUp,
      regulatedMeshModulusFromEventFlow (regulatedMeshModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G T I H C P N =>
      change
        some
          (RegulatedMeshModulusUp.mk
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist F))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist G))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist T))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist I))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist H))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist C))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist P))
            (regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist N))) =
          some (RegulatedMeshModulusUp.mk F G T I H C P N)
      rw [RegulatedMeshModulusTasteGate_single_carrier_alignment_decode F,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode G,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode T,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode I,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode H,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode C,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode P,
        RegulatedMeshModulusTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedMeshModulusTasteGate_single_carrier_alignment_injective
    {x y : RegulatedMeshModulusUp} :
    regulatedMeshModulusToEventFlow x = regulatedMeshModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedMeshModulusFromEventFlow (regulatedMeshModulusToEventFlow x) =
        regulatedMeshModulusFromEventFlow (regulatedMeshModulusToEventFlow y) :=
    congrArg regulatedMeshModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedMeshModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedMeshModulusTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedMeshModulusBHistCarrier : BHistCarrier RegulatedMeshModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedMeshModulusToEventFlow
  fromEventFlow := regulatedMeshModulusFromEventFlow

instance regulatedMeshModulusChapterTasteGate :
    ChapterTasteGate RegulatedMeshModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedMeshModulusFromEventFlow (regulatedMeshModulusToEventFlow x) = some x
    exact RegulatedMeshModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedMeshModulusTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegulatedMeshModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedMeshModulusChapterTasteGate

theorem RegulatedMeshModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, regulatedMeshModulusDecodeBHist (regulatedMeshModulusEncodeBHist h) = h) ∧
      (∀ x : RegulatedMeshModulusUp,
        regulatedMeshModulusFromEventFlow (regulatedMeshModulusToEventFlow x) = some x) ∧
        (∀ x y : RegulatedMeshModulusUp,
          regulatedMeshModulusToEventFlow x = regulatedMeshModulusToEventFlow y → x = y) ∧
          regulatedMeshModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegulatedMeshModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact RegulatedMeshModulusTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RegulatedMeshModulusTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.RegulatedMeshModulusUp

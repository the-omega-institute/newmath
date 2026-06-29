import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaximumModulusPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MaximumModulusPrincipleUp : Type where
  | mk (D F B R U H C P N : BHist) : MaximumModulusPrincipleUp

def maximumModulusPrincipleEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: maximumModulusPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: maximumModulusPrincipleEncodeBHist h

def maximumModulusPrincipleDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (maximumModulusPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (maximumModulusPrincipleDecodeBHist tail)

private theorem MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def maximumModulusPrincipleFields : MaximumModulusPrincipleUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MaximumModulusPrincipleUp.mk D F B R U H C P N => [D, F, B, R, U, H, C, P, N]

def maximumModulusPrincipleToEventFlow : MaximumModulusPrincipleUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (maximumModulusPrincipleFields x).map maximumModulusPrincipleEncodeBHist

def maximumModulusPrincipleFromEventFlow : EventFlow -> Option MaximumModulusPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: restD =>
      match restD with
      | F :: restF =>
          match restF with
          | B :: restB =>
              match restB with
              | R :: restR =>
                  match restR with
                  | U :: restU =>
                      match restU with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (MaximumModulusPrincipleUp.mk
                                              (maximumModulusPrincipleDecodeBHist D)
                                              (maximumModulusPrincipleDecodeBHist F)
                                              (maximumModulusPrincipleDecodeBHist B)
                                              (maximumModulusPrincipleDecodeBHist R)
                                              (maximumModulusPrincipleDecodeBHist U)
                                              (maximumModulusPrincipleDecodeBHist H)
                                              (maximumModulusPrincipleDecodeBHist C)
                                              (maximumModulusPrincipleDecodeBHist P)
                                              (maximumModulusPrincipleDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem MaximumModulusPrincipleTasteGate_single_carrier_alignment_round_trip :
    forall x : MaximumModulusPrincipleUp,
      maximumModulusPrincipleFromEventFlow (maximumModulusPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D F B R U H C P N =>
      change
        some
            (MaximumModulusPrincipleUp.mk
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist D))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist F))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist B))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist R))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist U))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist H))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist C))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist P))
              (maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist N))) =
          some (MaximumModulusPrincipleUp.mk D F B R U H C P N)
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode D]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode F]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode B]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode R]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode U]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode H]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode C]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode P]
      rw [MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode N]

private theorem MaximumModulusPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MaximumModulusPrincipleUp} :
    maximumModulusPrincipleToEventFlow x = maximumModulusPrincipleToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      maximumModulusPrincipleFromEventFlow (maximumModulusPrincipleToEventFlow x) =
        maximumModulusPrincipleFromEventFlow (maximumModulusPrincipleToEventFlow y) :=
    congrArg maximumModulusPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MaximumModulusPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MaximumModulusPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance maximumModulusPrincipleBHistCarrier : BHistCarrier MaximumModulusPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := maximumModulusPrincipleToEventFlow
  fromEventFlow := maximumModulusPrincipleFromEventFlow

instance maximumModulusPrincipleChapterTasteGate :
    ChapterTasteGate MaximumModulusPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change maximumModulusPrincipleFromEventFlow (maximumModulusPrincipleToEventFlow x) = some x
    exact MaximumModulusPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MaximumModulusPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MaximumModulusPrincipleTasteGate_single_carrier_alignment :
    (forall h : BHist,
        maximumModulusPrincipleDecodeBHist (maximumModulusPrincipleEncodeBHist h) = h) ∧
      (forall x : MaximumModulusPrincipleUp,
        maximumModulusPrincipleFromEventFlow (maximumModulusPrincipleToEventFlow x) = some x) ∧
      (forall x y : MaximumModulusPrincipleUp,
        maximumModulusPrincipleToEventFlow x = maximumModulusPrincipleToEventFlow y -> x = y) ∧
      maximumModulusPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MaximumModulusPrincipleTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact MaximumModulusPrincipleTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact MaximumModulusPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.MaximumModulusPrincipleUp

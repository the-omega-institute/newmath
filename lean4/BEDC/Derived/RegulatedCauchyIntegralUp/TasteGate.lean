import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedCauchyIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedCauchyIntegralUp : Type where
  | mk (G T A W R E H C P N : BHist) : RegulatedCauchyIntegralUp
  deriving DecidableEq

def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist h

def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fields :
    RegulatedCauchyIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedCauchyIntegralUp.mk G T A W R E H C P N => [G, T, A, W, R, E, H, C, P, N]

def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow :
    RegulatedCauchyIntegralUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fields x).map
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist

def RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegulatedCauchyIntegralUp
  -- BEDC touchpoint anchor: BHist BMark
  | G :: restG =>
      match restG with
      | T :: restT =>
          match restT with
          | A :: restA =>
              match restA with
              | W :: restW =>
                  match restW with
                  | R :: restR =>
                      match restR with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (RegulatedCauchyIntegralUp.mk
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist G)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist T)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist A)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist W)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist R)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist E)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist H)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist C)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist P)
                                                  (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist N))
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
  | [] => none

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip
    (x : RegulatedCauchyIntegralUp) :
    RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow
        (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G T A W R E H C P N =>
      change
        some
          (RegulatedCauchyIntegralUp.mk
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist G))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist T))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist A))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist W))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist R))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist E))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist H))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist C))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist P))
            (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decodeBHist
              (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RegulatedCauchyIntegralUp.mk G T A W R E H C P N)
      rw [RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode G,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode T,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode A,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode W,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode R,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode E,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode H,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode C,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode P,
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedCauchyIntegralUp} :
    RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow x =
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedCauchyIntegralBHistCarrier :
    BHistCarrier RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow

instance regulatedCauchyIntegralChapterTasteGate :
    ChapterTasteGate RegulatedCauchyIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegulatedCauchyIntegralTasteGate_single_carrier_alignment_fromEventFlow
          (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegulatedCauchyIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedCauchyIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegulatedCauchyIntegralTasteGate_single_carrier_alignment :
    ChapterTasteGate RegulatedCauchyIntegralUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact regulatedCauchyIntegralChapterTasteGate

end BEDC.Derived.RegulatedCauchyIntegralUp

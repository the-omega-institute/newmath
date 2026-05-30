import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SturmComparisonUp : Type where
  | mk (O0 O1 K Z W R E H C P N : BHist) : SturmComparisonUp
  deriving DecidableEq

def SturmComparisonTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: SturmComparisonTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: SturmComparisonTasteGate_single_carrier_alignment_encodeBHist h

def SturmComparisonTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SturmComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
          (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SturmComparisonTasteGate_single_carrier_alignment_fields :
    SturmComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SturmComparisonUp.mk O0 O1 K Z W R E H C P N => [O0, O1, K, Z, W, R, E, H, C, P, N]

def SturmComparisonTasteGate_single_carrier_alignment_toEventFlow :
    SturmComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (SturmComparisonTasteGate_single_carrier_alignment_fields x).map
        SturmComparisonTasteGate_single_carrier_alignment_encodeBHist

def SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option SturmComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | O0 :: restO0 =>
      match restO0 with
      | O1 :: restO1 =>
          match restO1 with
          | K :: restK =>
              match restK with
              | Z :: restZ =>
                  match restZ with
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
                                                    (SturmComparisonUp.mk
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist O0)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist O1)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist K)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist Z)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist W)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist R)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist E)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist H)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist C)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist P)
                                                      (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist N))
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
  | [] => none

private theorem SturmComparisonTasteGate_single_carrier_alignment_round_trip
    (x : SturmComparisonUp) :
    SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow
        (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O0 O1 K Z W R E H C P N =>
      change
        some
          (SturmComparisonUp.mk
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist O0))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist O1))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist K))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist Z))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist W))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist R))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist E))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist H))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist C))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist P))
            (SturmComparisonTasteGate_single_carrier_alignment_decodeBHist
              (SturmComparisonTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SturmComparisonUp.mk O0 O1 K Z W R E H C P N)
      rw [SturmComparisonTasteGate_single_carrier_alignment_decode_encode O0,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode O1,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode K,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode Z,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode W,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode R,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode E,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode H,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode C,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode P,
        SturmComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem SturmComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SturmComparisonUp} :
    SturmComparisonTasteGate_single_carrier_alignment_toEventFlow x =
        SturmComparisonTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow
          (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow x) =
        SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow
          (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SturmComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SturmComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance sturmComparisonBHistCarrier : BHistCarrier SturmComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SturmComparisonTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow

instance sturmComparisonChapterTasteGate : ChapterTasteGate SturmComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SturmComparisonTasteGate_single_carrier_alignment_fromEventFlow
          (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact SturmComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SturmComparisonTasteGate_single_carrier_alignment :
    ChapterTasteGate SturmComparisonUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact sturmComparisonChapterTasteGate

end BEDC.Derived.SturmComparisonUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBallCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBallCompactnessUp : Type where
  | mk (B P N K T M R H D Q A : BHist) : ClosedBallCompactnessUp
  deriving DecidableEq

def closedBallCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBallCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBallCompactnessEncodeBHist h

def closedBallCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBallCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBallCompactnessDecodeBHist tail)

private theorem ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedBallCompactnessToEventFlow : ClosedBallCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBallCompactnessUp.mk B P N K T M R H D Q A =>
      [[BMark.b0],
        closedBallCompactnessEncodeBHist B,
        closedBallCompactnessEncodeBHist P,
        closedBallCompactnessEncodeBHist N,
        closedBallCompactnessEncodeBHist K,
        closedBallCompactnessEncodeBHist T,
        closedBallCompactnessEncodeBHist M,
        closedBallCompactnessEncodeBHist R,
        closedBallCompactnessEncodeBHist H,
        closedBallCompactnessEncodeBHist D,
        closedBallCompactnessEncodeBHist Q,
        closedBallCompactnessEncodeBHist A]

def closedBallCompactnessFromEventFlow : EventFlow → Option ClosedBallCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | B :: rest =>
          match rest with
          | [] => none
          | P :: rest =>
              match rest with
              | [] => none
              | N :: rest =>
                  match rest with
                  | [] => none
                  | K :: rest =>
                      match rest with
                      | [] => none
                      | T :: rest =>
                          match rest with
                          | [] => none
                          | M :: rest =>
                              match rest with
                              | [] => none
                              | R :: rest =>
                                  match rest with
                                  | [] => none
                                  | H :: rest =>
                                      match rest with
                                      | [] => none
                                      | D :: rest =>
                                          match rest with
                                          | [] => none
                                          | Q :: rest =>
                                              match rest with
                                              | [] => none
                                              | A :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (ClosedBallCompactnessUp.mk
                                                          (closedBallCompactnessDecodeBHist B)
                                                          (closedBallCompactnessDecodeBHist P)
                                                          (closedBallCompactnessDecodeBHist N)
                                                          (closedBallCompactnessDecodeBHist K)
                                                          (closedBallCompactnessDecodeBHist T)
                                                          (closedBallCompactnessDecodeBHist M)
                                                          (closedBallCompactnessDecodeBHist R)
                                                          (closedBallCompactnessDecodeBHist H)
                                                          (closedBallCompactnessDecodeBHist D)
                                                          (closedBallCompactnessDecodeBHist Q)
                                                          (closedBallCompactnessDecodeBHist A))
                                                  | _ :: _ => none

private theorem ClosedBallCompactnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedBallCompactnessUp,
      closedBallCompactnessFromEventFlow
        (closedBallCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B P N K T M R H D Q A =>
      change
        some
          (ClosedBallCompactnessUp.mk
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist B))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist P))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist N))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist K))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist T))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist M))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist R))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist H))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist D))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist Q))
            (closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist A))) =
          some (ClosedBallCompactnessUp.mk B P N K T M R H D Q A)
      rw [ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode B,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode P,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode N,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode K,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode T,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode M,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode R,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode H,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode D,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode Q,
        ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode A]

private theorem ClosedBallCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedBallCompactnessUp} :
    closedBallCompactnessToEventFlow x = closedBallCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBallCompactnessFromEventFlow (closedBallCompactnessToEventFlow x) =
        closedBallCompactnessFromEventFlow (closedBallCompactnessToEventFlow y) :=
    congrArg closedBallCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedBallCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedBallCompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance closedBallCompactnessBHistCarrier :
    BHistCarrier ClosedBallCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBallCompactnessToEventFlow
  fromEventFlow := closedBallCompactnessFromEventFlow

instance closedBallCompactnessChapterTasteGate :
    ChapterTasteGate ClosedBallCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedBallCompactnessFromEventFlow
        (closedBallCompactnessToEventFlow x) = some x
    exact ClosedBallCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedBallCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ClosedBallCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedBallCompactnessDecodeBHist (closedBallCompactnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedBallCompactnessUp) ∧
        Nonempty (ChapterTasteGate ClosedBallCompactnessUp) ∧
          closedBallCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ClosedBallCompactnessTasteGate_single_carrier_alignment_decode_encode,
      ⟨closedBallCompactnessBHistCarrier⟩,
      ⟨closedBallCompactnessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ClosedBallCompactnessUp

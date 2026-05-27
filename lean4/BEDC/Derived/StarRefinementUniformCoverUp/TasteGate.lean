import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StarRefinementUniformCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StarRefinementUniformCoverUp : Type where
  | mk
      (U E F R M H C P N : BHist) :
      StarRefinementUniformCoverUp
  deriving DecidableEq

def starRefinementUniformCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: starRefinementUniformCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: starRefinementUniformCoverEncodeBHist h

def starRefinementUniformCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (starRefinementUniformCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (starRefinementUniformCoverDecodeBHist tail)

private theorem StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      starRefinementUniformCoverDecodeBHist (starRefinementUniformCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def starRefinementUniformCoverToEventFlow : StarRefinementUniformCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StarRefinementUniformCoverUp.mk U E F R M H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        starRefinementUniformCoverEncodeBHist U,
        starRefinementUniformCoverEncodeBHist E,
        starRefinementUniformCoverEncodeBHist F,
        starRefinementUniformCoverEncodeBHist R,
        starRefinementUniformCoverEncodeBHist M,
        starRefinementUniformCoverEncodeBHist H,
        starRefinementUniformCoverEncodeBHist C,
        starRefinementUniformCoverEncodeBHist P,
        starRefinementUniformCoverEncodeBHist N]

def starRefinementUniformCoverFromEventFlow : EventFlow → Option StarRefinementUniformCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restU =>
      match restU with
      | [] => none
      | U :: restE =>
          match restE with
          | [] => none
          | E :: restF =>
              match restF with
              | [] => none
              | F :: restR =>
                  match restR with
                  | [] => none
                  | R :: restM =>
                      match restM with
                      | [] => none
                      | M :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (StarRefinementUniformCoverUp.mk
                                                  (starRefinementUniformCoverDecodeBHist U)
                                                  (starRefinementUniformCoverDecodeBHist E)
                                                  (starRefinementUniformCoverDecodeBHist F)
                                                  (starRefinementUniformCoverDecodeBHist R)
                                                  (starRefinementUniformCoverDecodeBHist M)
                                                  (starRefinementUniformCoverDecodeBHist H)
                                                  (starRefinementUniformCoverDecodeBHist C)
                                                  (starRefinementUniformCoverDecodeBHist P)
                                                  (starRefinementUniformCoverDecodeBHist N))
                                          | _ :: _ => none

private theorem StarRefinementUniformCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StarRefinementUniformCoverUp,
      starRefinementUniformCoverFromEventFlow
        (starRefinementUniformCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U E F R M H C P N =>
      change
        some
          (StarRefinementUniformCoverUp.mk
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist U))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist E))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist F))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist R))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist M))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist H))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist C))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist P))
            (starRefinementUniformCoverDecodeBHist
              (starRefinementUniformCoverEncodeBHist N))) =
          some (StarRefinementUniformCoverUp.mk U E F R M H C P N)
      rw [StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode U,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode E,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode F,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode R,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode M,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode H,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode C,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode P,
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem StarRefinementUniformCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StarRefinementUniformCoverUp} :
    starRefinementUniformCoverToEventFlow x = starRefinementUniformCoverToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      starRefinementUniformCoverFromEventFlow (starRefinementUniformCoverToEventFlow x) =
        starRefinementUniformCoverFromEventFlow (starRefinementUniformCoverToEventFlow y) :=
    congrArg starRefinementUniformCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StarRefinementUniformCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StarRefinementUniformCoverTasteGate_single_carrier_alignment_round_trip y)))

instance starRefinementUniformCoverBHistCarrier :
    BHistCarrier StarRefinementUniformCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := starRefinementUniformCoverToEventFlow
  fromEventFlow := starRefinementUniformCoverFromEventFlow

instance starRefinementUniformCoverChapterTasteGate :
    ChapterTasteGate StarRefinementUniformCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      starRefinementUniformCoverFromEventFlow
        (starRefinementUniformCoverToEventFlow x) = some x
    exact StarRefinementUniformCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (StarRefinementUniformCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem StarRefinementUniformCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      starRefinementUniformCoverDecodeBHist (starRefinementUniformCoverEncodeBHist h) = h) ∧
      (∀ x : StarRefinementUniformCoverUp,
        starRefinementUniformCoverFromEventFlow
          (starRefinementUniformCoverToEventFlow x) = some x) ∧
        (∀ x y : StarRefinementUniformCoverUp,
          starRefinementUniformCoverToEventFlow x =
            starRefinementUniformCoverToEventFlow y → x = y) ∧
          starRefinementUniformCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨StarRefinementUniformCoverTasteGate_single_carrier_alignment_decode_encode,
      StarRefinementUniformCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        StarRefinementUniformCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StarRefinementUniformCoverUp

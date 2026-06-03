import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionCriterionUp : Type where
  | mk (D S R E M L H C P N : BHist) : LocatedCompletionCriterionUp
  deriving DecidableEq

def locatedCompletionCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionCriterionEncodeBHist h

def locatedCompletionCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionCriterionDecodeBHist tail)

private theorem LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionCriterionToEventFlow : LocatedCompletionCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionCriterionUp.mk D S R E M L H C P N =>
      [locatedCompletionCriterionEncodeBHist D, locatedCompletionCriterionEncodeBHist S,
        locatedCompletionCriterionEncodeBHist R, locatedCompletionCriterionEncodeBHist E,
        locatedCompletionCriterionEncodeBHist M, locatedCompletionCriterionEncodeBHist L,
        locatedCompletionCriterionEncodeBHist H, locatedCompletionCriterionEncodeBHist C,
        locatedCompletionCriterionEncodeBHist P, locatedCompletionCriterionEncodeBHist N]

def locatedCompletionCriterionFromEventFlow (flow : EventFlow) : Option LocatedCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (LocatedCompletionCriterionUp.mk
                                                  (locatedCompletionCriterionDecodeBHist D)
                                                  (locatedCompletionCriterionDecodeBHist S)
                                                  (locatedCompletionCriterionDecodeBHist R)
                                                  (locatedCompletionCriterionDecodeBHist E)
                                                  (locatedCompletionCriterionDecodeBHist M)
                                                  (locatedCompletionCriterionDecodeBHist L)
                                                  (locatedCompletionCriterionDecodeBHist H)
                                                  (locatedCompletionCriterionDecodeBHist C)
                                                  (locatedCompletionCriterionDecodeBHist P)
                                                  (locatedCompletionCriterionDecodeBHist N))
                                          | _ :: _ => none

private theorem LocatedCompletionCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompletionCriterionUp,
      locatedCompletionCriterionFromEventFlow (locatedCompletionCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E M L H C P N =>
      change
        some
          (LocatedCompletionCriterionUp.mk
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist D))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist S))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist R))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist E))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist M))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist L))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist H))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist C))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist P))
            (locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist N))) =
          some (LocatedCompletionCriterionUp.mk D S R E M L H C P N)
      rw [LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode D,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode S,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode R,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode E,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode M,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode L,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode H,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode C,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode P,
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedCompletionCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionCriterionUp} :
    locatedCompletionCriterionToEventFlow x = locatedCompletionCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionCriterionFromEventFlow (locatedCompletionCriterionToEventFlow x) =
        locatedCompletionCriterionFromEventFlow (locatedCompletionCriterionToEventFlow y) :=
    congrArg locatedCompletionCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCompletionCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompletionCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompletionCriterionBHistCarrier : BHistCarrier LocatedCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionCriterionToEventFlow
  fromEventFlow := locatedCompletionCriterionFromEventFlow

instance locatedCompletionCriterionChapterTasteGate :
    ChapterTasteGate LocatedCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionCriterionFromEventFlow (locatedCompletionCriterionToEventFlow x) =
      some x
    exact LocatedCompletionCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCompletionCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompletionCriterionChapterTasteGate

theorem LocatedCompletionCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCompletionCriterionDecodeBHist (locatedCompletionCriterionEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionCriterionUp,
        locatedCompletionCriterionFromEventFlow (locatedCompletionCriterionToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedCompletionCriterionUp,
          locatedCompletionCriterionToEventFlow x =
            locatedCompletionCriterionToEventFlow y → x = y) ∧
          locatedCompletionCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedCompletionCriterionTasteGate_single_carrier_alignment_decode_encode,
      LocatedCompletionCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedCompletionCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCompletionCriterionUp

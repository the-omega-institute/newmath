import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# BishopLocatedRealCompletionUp TasteGate carrier.
-/

namespace BEDC.Derived.BishopLocatedRealCompletionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Bishop located-real completion packet with the nine displayed rows. -/
inductive BishopLocatedRealCompletionUp : Type where
  | mk : (D S R L E H C P N : BHist) → BishopLocatedRealCompletionUp
  deriving DecidableEq

def bishopLocatedRealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRealCompletionEncodeBHist h

def bishopLocatedRealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRealCompletionDecodeBHist tail)

private theorem BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopLocatedRealCompletionDecodeBHist
        (bishopLocatedRealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedRealCompletionToEventFlow :
    BishopLocatedRealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRealCompletionUp.mk D S R L E H C P N =>
      [[BMark.b0],
        bishopLocatedRealCompletionEncodeBHist D,
        [BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopLocatedRealCompletionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopLocatedRealCompletionEncodeBHist N]

private def bishopLocatedRealCompletionDecodeRows :
    EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match bishopLocatedRealCompletionDecodeRows rest1 with
          | some rows => some (bishopLocatedRealCompletionDecodeBHist row :: rows)
          | none => none

private def bishopLocatedRealCompletionFromRows :
    List BHist → Option BishopLocatedRealCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
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
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some (BishopLocatedRealCompletionUp.mk
                                            D S R L E H C P N)
                                      | _ :: _ => none

def bishopLocatedRealCompletionFromEventFlow :
    EventFlow → Option BishopLocatedRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    match bishopLocatedRealCompletionDecodeRows ef with
    | some rows => bishopLocatedRealCompletionFromRows rows
    | none => none

private theorem BishopLocatedRealCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedRealCompletionUp,
      bishopLocatedRealCompletionFromEventFlow
        (bishopLocatedRealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R L E H C P N =>
      change
        some
          (BishopLocatedRealCompletionUp.mk
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist D))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist S))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist R))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist L))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist E))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist H))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist C))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist P))
            (bishopLocatedRealCompletionDecodeBHist
              (bishopLocatedRealCompletionEncodeBHist N))) =
          some (BishopLocatedRealCompletionUp.mk D S R L E H C P N)
      rw [BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode L,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopLocatedRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedRealCompletionUp} :
    bishopLocatedRealCompletionToEventFlow x =
      bishopLocatedRealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedRealCompletionFromEventFlow
          (bishopLocatedRealCompletionToEventFlow x) =
        bishopLocatedRealCompletionFromEventFlow
          (bishopLocatedRealCompletionToEventFlow y) :=
    congrArg bishopLocatedRealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedRealCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedRealCompletionBHistCarrier :
    BHistCarrier BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedRealCompletionToEventFlow
  fromEventFlow := bishopLocatedRealCompletionFromEventFlow

instance bishopLocatedRealCompletionChapterTasteGate :
    ChapterTasteGate BishopLocatedRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedRealCompletionFromEventFlow
        (bishopLocatedRealCompletionToEventFlow x) = some x
    exact BishopLocatedRealCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

/-- Public TasteGate object for the Bishop located-real completion carrier. -/
def taste_gate : ChapterTasteGate BishopLocatedRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedRealCompletionChapterTasteGate

theorem BishopLocatedRealCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopLocatedRealCompletionDecodeBHist
          (bishopLocatedRealCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedRealCompletionUp,
        bishopLocatedRealCompletionFromEventFlow
          (bishopLocatedRealCompletionToEventFlow x) = some x) ∧
      (∀ x y : BishopLocatedRealCompletionUp,
        bishopLocatedRealCompletionToEventFlow x =
          bishopLocatedRealCompletionToEventFlow y → x = y) ∧
      bishopLocatedRealCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopLocatedRealCompletionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BishopLocatedRealCompletionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          BishopLocatedRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.BishopLocatedRealCompletionUp

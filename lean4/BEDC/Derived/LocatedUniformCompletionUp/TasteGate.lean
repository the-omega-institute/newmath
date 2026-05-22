import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformCompletionUp : Type where
  | mk : (F U B S R E H C P N : BHist) → LocatedUniformCompletionUp
  deriving DecidableEq

def locatedUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformCompletionEncodeBHist h

def locatedUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformCompletionDecodeBHist tail)

private theorem locatedUniformCompletion_decode_encode_bhist :
    ∀ h : BHist,
      locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformCompletionFields : LocatedUniformCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformCompletionUp.mk F U B S R E H C P N => [F, U, B, S, R, E, H, C, P, N]

def locatedUniformCompletionToEventFlow : LocatedUniformCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedUniformCompletionFields x).map locatedUniformCompletionEncodeBHist

def locatedUniformCompletionFromEventFlow : EventFlow → Option LocatedUniformCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (LocatedUniformCompletionUp.mk
                                                  (locatedUniformCompletionDecodeBHist F)
                                                  (locatedUniformCompletionDecodeBHist U)
                                                  (locatedUniformCompletionDecodeBHist B)
                                                  (locatedUniformCompletionDecodeBHist S)
                                                  (locatedUniformCompletionDecodeBHist R)
                                                  (locatedUniformCompletionDecodeBHist E)
                                                  (locatedUniformCompletionDecodeBHist H)
                                                  (locatedUniformCompletionDecodeBHist C)
                                                  (locatedUniformCompletionDecodeBHist P)
                                                  (locatedUniformCompletionDecodeBHist N))
                                          | _ :: _ => none

private theorem locatedUniformCompletion_round_trip :
    ∀ x : LocatedUniformCompletionUp,
      locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U B S R E H C P N =>
      change
        some
            (LocatedUniformCompletionUp.mk
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist F))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist U))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist B))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist S))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist R))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist E))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist H))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist C))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist P))
              (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist N))) =
          some (LocatedUniformCompletionUp.mk F U B S R E H C P N)
      rw [locatedUniformCompletion_decode_encode_bhist F,
        locatedUniformCompletion_decode_encode_bhist U,
        locatedUniformCompletion_decode_encode_bhist B,
        locatedUniformCompletion_decode_encode_bhist S,
        locatedUniformCompletion_decode_encode_bhist R,
        locatedUniformCompletion_decode_encode_bhist E,
        locatedUniformCompletion_decode_encode_bhist H,
        locatedUniformCompletion_decode_encode_bhist C,
        locatedUniformCompletion_decode_encode_bhist P,
        locatedUniformCompletion_decode_encode_bhist N]

private theorem locatedUniformCompletionToEventFlow_injective
    {x y : LocatedUniformCompletionUp} :
    locatedUniformCompletionToEventFlow x = locatedUniformCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) =
        locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow y) :=
    congrArg locatedUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedUniformCompletion_round_trip x).symm
      (Eq.trans hread (locatedUniformCompletion_round_trip y)))

instance locatedUniformCompletionBHistCarrier : BHistCarrier LocatedUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformCompletionToEventFlow
  fromEventFlow := locatedUniformCompletionFromEventFlow

instance locatedUniformCompletionChapterTasteGate :
    ChapterTasteGate LocatedUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) = some x
    exact locatedUniformCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedUniformCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedUniformCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedUniformCompletionChapterTasteGate

theorem LocatedUniformCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist h) = h) ∧
      (∀ x : LocatedUniformCompletionUp,
        locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) = some x) ∧
        (∀ x y : LocatedUniformCompletionUp,
          locatedUniformCompletionToEventFlow x = locatedUniformCompletionToEventFlow y → x = y) ∧
          locatedUniformCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedUniformCompletion_decode_encode_bhist,
      locatedUniformCompletion_round_trip,
      (fun _ _ heq => locatedUniformCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedUniformCompletionUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealOrderCompletionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealOrderCompletionBoundaryUp : Type where
  | mk (L U D S R E H C P N : BHist) : RealOrderCompletionBoundaryUp
  deriving DecidableEq

def realOrderCompletionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realOrderCompletionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realOrderCompletionBoundaryEncodeBHist h

def realOrderCompletionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realOrderCompletionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realOrderCompletionBoundaryDecodeBHist tail)

private theorem realOrderCompletionBoundary_decode_encode :
    ∀ h : BHist,
      realOrderCompletionBoundaryDecodeBHist (realOrderCompletionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realOrderCompletionBoundaryToEventFlow :
    RealOrderCompletionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealOrderCompletionBoundaryUp.mk L U D S R E H C P N =>
      [realOrderCompletionBoundaryEncodeBHist L,
        realOrderCompletionBoundaryEncodeBHist U,
        realOrderCompletionBoundaryEncodeBHist D,
        realOrderCompletionBoundaryEncodeBHist S,
        realOrderCompletionBoundaryEncodeBHist R,
        realOrderCompletionBoundaryEncodeBHist E,
        realOrderCompletionBoundaryEncodeBHist H,
        realOrderCompletionBoundaryEncodeBHist C,
        realOrderCompletionBoundaryEncodeBHist P,
        realOrderCompletionBoundaryEncodeBHist N]

def realOrderCompletionBoundaryFromEventFlow
    (flow : EventFlow) : Option RealOrderCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | L :: rest =>
      match rest with
      | [] => none
      | U :: rest =>
          match rest with
          | [] => none
          | D :: rest =>
              match rest with
              | [] => none
              | S :: rest =>
                  match rest with
                  | [] => none
                  | R :: rest =>
                      match rest with
                      | [] => none
                      | E :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (RealOrderCompletionBoundaryUp.mk
                                                  (realOrderCompletionBoundaryDecodeBHist L)
                                                  (realOrderCompletionBoundaryDecodeBHist U)
                                                  (realOrderCompletionBoundaryDecodeBHist D)
                                                  (realOrderCompletionBoundaryDecodeBHist S)
                                                  (realOrderCompletionBoundaryDecodeBHist R)
                                                  (realOrderCompletionBoundaryDecodeBHist E)
                                                  (realOrderCompletionBoundaryDecodeBHist H)
                                                  (realOrderCompletionBoundaryDecodeBHist C)
                                                  (realOrderCompletionBoundaryDecodeBHist P)
                                                  (realOrderCompletionBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem realOrderCompletionBoundary_round_trip :
    ∀ x : RealOrderCompletionBoundaryUp,
      realOrderCompletionBoundaryFromEventFlow
          (realOrderCompletionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U D S R E H C P N =>
      rw [realOrderCompletionBoundaryToEventFlow, realOrderCompletionBoundaryFromEventFlow,
        realOrderCompletionBoundary_decode_encode L,
        realOrderCompletionBoundary_decode_encode U,
        realOrderCompletionBoundary_decode_encode D,
        realOrderCompletionBoundary_decode_encode S,
        realOrderCompletionBoundary_decode_encode R,
        realOrderCompletionBoundary_decode_encode E,
        realOrderCompletionBoundary_decode_encode H,
        realOrderCompletionBoundary_decode_encode C,
        realOrderCompletionBoundary_decode_encode P,
        realOrderCompletionBoundary_decode_encode N]

private theorem realOrderCompletionBoundaryToEventFlow_injective
    {x y : RealOrderCompletionBoundaryUp} :
    realOrderCompletionBoundaryToEventFlow x =
        realOrderCompletionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realOrderCompletionBoundaryFromEventFlow
          (realOrderCompletionBoundaryToEventFlow x) =
        realOrderCompletionBoundaryFromEventFlow
          (realOrderCompletionBoundaryToEventFlow y) :=
    congrArg realOrderCompletionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realOrderCompletionBoundary_round_trip x).symm
      (Eq.trans hread (realOrderCompletionBoundary_round_trip y)))

instance realOrderCompletionBoundaryBHistCarrier :
    BHistCarrier RealOrderCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realOrderCompletionBoundaryToEventFlow
  fromEventFlow := realOrderCompletionBoundaryFromEventFlow

instance realOrderCompletionBoundaryChapterTasteGate :
    ChapterTasteGate RealOrderCompletionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realOrderCompletionBoundaryFromEventFlow
          (realOrderCompletionBoundaryToEventFlow x) =
        some x
    exact realOrderCompletionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realOrderCompletionBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealOrderCompletionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realOrderCompletionBoundaryChapterTasteGate

theorem RealOrderCompletionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realOrderCompletionBoundaryDecodeBHist
          (realOrderCompletionBoundaryEncodeBHist h) =
        h) ∧
      (∀ x : RealOrderCompletionBoundaryUp,
        realOrderCompletionBoundaryFromEventFlow
            (realOrderCompletionBoundaryToEventFlow x) =
          some x) ∧
      (∀ x y : RealOrderCompletionBoundaryUp,
        realOrderCompletionBoundaryToEventFlow x =
            realOrderCompletionBoundaryToEventFlow y →
          x = y) ∧
      realOrderCompletionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realOrderCompletionBoundary_decode_encode,
      realOrderCompletionBoundary_round_trip,
      fun _ _ heq => realOrderCompletionBoundaryToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealOrderCompletionBoundaryUp

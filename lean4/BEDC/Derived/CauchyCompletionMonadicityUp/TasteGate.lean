import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionMonadicityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionMonadicityUp : Type where
  | mk (T A K U D W R Q E H C P N : BHist) : CauchyCompletionMonadicityUp
  deriving DecidableEq

def cauchyCompletionMonadicityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionMonadicityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionMonadicityEncodeBHist h

def cauchyCompletionMonadicityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionMonadicityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionMonadicityDecodeBHist tail)

private theorem cauchyCompletionMonadicity_decode_encode :
    ∀ h : BHist,
      cauchyCompletionMonadicityDecodeBHist
          (cauchyCompletionMonadicityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionMonadicityFields :
    CauchyCompletionMonadicityUp -> List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CauchyCompletionMonadicityUp.mk T A K U D W R Q E H C P N =>
      [T, A, K, U, D, W, R, Q, E, H, C, P, N]

def cauchyCompletionMonadicityToEventFlow :
    CauchyCompletionMonadicityUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CauchyCompletionMonadicityUp.mk T A K U D W R Q E H C P N =>
      [cauchyCompletionMonadicityEncodeBHist T,
        cauchyCompletionMonadicityEncodeBHist A,
        cauchyCompletionMonadicityEncodeBHist K,
        cauchyCompletionMonadicityEncodeBHist U,
        cauchyCompletionMonadicityEncodeBHist D,
        cauchyCompletionMonadicityEncodeBHist W,
        cauchyCompletionMonadicityEncodeBHist R,
        cauchyCompletionMonadicityEncodeBHist Q,
        cauchyCompletionMonadicityEncodeBHist E,
        cauchyCompletionMonadicityEncodeBHist H,
        cauchyCompletionMonadicityEncodeBHist C,
        cauchyCompletionMonadicityEncodeBHist P,
        cauchyCompletionMonadicityEncodeBHist N]

def cauchyCompletionMonadicityFromEventFlow :
    EventFlow -> Option CauchyCompletionMonadicityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | T :: A :: K :: U :: D :: W :: R :: Q :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyCompletionMonadicityUp.mk
          (cauchyCompletionMonadicityDecodeBHist T)
          (cauchyCompletionMonadicityDecodeBHist A)
          (cauchyCompletionMonadicityDecodeBHist K)
          (cauchyCompletionMonadicityDecodeBHist U)
          (cauchyCompletionMonadicityDecodeBHist D)
          (cauchyCompletionMonadicityDecodeBHist W)
          (cauchyCompletionMonadicityDecodeBHist R)
          (cauchyCompletionMonadicityDecodeBHist Q)
          (cauchyCompletionMonadicityDecodeBHist E)
          (cauchyCompletionMonadicityDecodeBHist H)
          (cauchyCompletionMonadicityDecodeBHist C)
          (cauchyCompletionMonadicityDecodeBHist P)
          (cauchyCompletionMonadicityDecodeBHist N))
  | _ => none

private theorem cauchyCompletionMonadicity_round_trip :
    ∀ x : CauchyCompletionMonadicityUp,
      cauchyCompletionMonadicityFromEventFlow
          (cauchyCompletionMonadicityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T A K U D W R Q E H C P N =>
      change
        some
            (CauchyCompletionMonadicityUp.mk
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist T))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist A))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist K))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist U))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist D))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist W))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist R))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist Q))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist E))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist H))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist C))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist P))
              (cauchyCompletionMonadicityDecodeBHist
                (cauchyCompletionMonadicityEncodeBHist N))) =
          some (CauchyCompletionMonadicityUp.mk T A K U D W R Q E H C P N)
      rw [cauchyCompletionMonadicity_decode_encode T,
        cauchyCompletionMonadicity_decode_encode A,
        cauchyCompletionMonadicity_decode_encode K,
        cauchyCompletionMonadicity_decode_encode U,
        cauchyCompletionMonadicity_decode_encode D,
        cauchyCompletionMonadicity_decode_encode W,
        cauchyCompletionMonadicity_decode_encode R,
        cauchyCompletionMonadicity_decode_encode Q,
        cauchyCompletionMonadicity_decode_encode E,
        cauchyCompletionMonadicity_decode_encode H,
        cauchyCompletionMonadicity_decode_encode C,
        cauchyCompletionMonadicity_decode_encode P,
        cauchyCompletionMonadicity_decode_encode N]

private theorem cauchyCompletionMonadicityToEventFlow_injective
    {x y : CauchyCompletionMonadicityUp} :
    cauchyCompletionMonadicityToEventFlow x =
        cauchyCompletionMonadicityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      cauchyCompletionMonadicityFromEventFlow
          (cauchyCompletionMonadicityToEventFlow x) =
        cauchyCompletionMonadicityFromEventFlow
          (cauchyCompletionMonadicityToEventFlow y) :=
    congrArg cauchyCompletionMonadicityFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (cauchyCompletionMonadicity_round_trip x).symm
      (Eq.trans hread (cauchyCompletionMonadicity_round_trip y)))

instance cauchyCompletionMonadicityBHistCarrier :
    BHistCarrier CauchyCompletionMonadicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionMonadicityToEventFlow
  fromEventFlow := cauchyCompletionMonadicityFromEventFlow

instance cauchyCompletionMonadicityChapterTasteGate :
    ChapterTasteGate CauchyCompletionMonadicityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionMonadicityFromEventFlow
          (cauchyCompletionMonadicityToEventFlow x) = some x
    exact cauchyCompletionMonadicity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionMonadicityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionMonadicityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionMonadicityChapterTasteGate

theorem CauchyCompletionMonadicityTasteGate_single_carrier_alignment
    {T A K U D W R Q E H C P N : BHist} :
    cauchyCompletionMonadicityEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      cauchyCompletionMonadicityDecodeBHist ([] : RawEvent) = BHist.Empty ∧
      cauchyCompletionMonadicityFields
          (CauchyCompletionMonadicityUp.mk T A K U D W R Q E H C P N) =
        [T, A, K, U, D, W, R, Q, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

end BEDC.Derived.CauchyCompletionMonadicityUp.TasteGate

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionRetractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionRetractionUp : Type where
  | mk (X U V A I G S D R E H C P N : BHist) : CauchyCompletionRetractionUp
  deriving DecidableEq

def cauchyCompletionRetractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionRetractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionRetractionEncodeBHist h

def cauchyCompletionRetractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionRetractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionRetractionDecodeBHist tail)

private theorem CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionRetractionDecodeBHist
        (cauchyCompletionRetractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionRetractionFields :
    CauchyCompletionRetractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionRetractionUp.mk X U V A I G S D R E H C P N =>
      [X, U, V, A, I, G, S, D, R, E, H, C, P, N]

def cauchyCompletionRetractionToEventFlow :
    CauchyCompletionRetractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionRetractionFields x).map cauchyCompletionRetractionEncodeBHist

private def CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault index rest

def cauchyCompletionRetractionFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionRetractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionRetractionUp.mk
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 12 ef))
      (cauchyCompletionRetractionDecodeBHist
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_eventAtDefault 13 ef)))

private theorem CauchyCompletionRetractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionRetractionUp,
      cauchyCompletionRetractionFromEventFlow
        (cauchyCompletionRetractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U V A I G S D R E H C P N =>
      change
        some
          (CauchyCompletionRetractionUp.mk
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist X))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist U))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist V))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist A))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist I))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist G))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist S))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist D))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist R))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist E))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist H))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist C))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist P))
            (cauchyCompletionRetractionDecodeBHist
              (cauchyCompletionRetractionEncodeBHist N))) =
          some (CauchyCompletionRetractionUp.mk X U V A I G S D R E H C P N)
      rw [CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode X,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode V,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode A,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode I,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode G,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionRetractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionRetractionUp} :
    cauchyCompletionRetractionToEventFlow x =
      cauchyCompletionRetractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionRetractionFromEventFlow
          (cauchyCompletionRetractionToEventFlow x) =
        cauchyCompletionRetractionFromEventFlow
          (cauchyCompletionRetractionToEventFlow y) :=
    congrArg cauchyCompletionRetractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionRetractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionRetractionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionRetractionBHistCarrier :
    BHistCarrier CauchyCompletionRetractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionRetractionToEventFlow
  fromEventFlow := cauchyCompletionRetractionFromEventFlow

instance cauchyCompletionRetractionChapterTasteGate :
    ChapterTasteGate CauchyCompletionRetractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionRetractionFromEventFlow
        (cauchyCompletionRetractionToEventFlow x) = some x
    exact CauchyCompletionRetractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionRetractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionRetractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionRetractionDecodeBHist
        (cauchyCompletionRetractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionRetractionUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionRetractionUp) ∧
          cauchyCompletionRetractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyCompletionRetractionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact Nonempty.intro cauchyCompletionRetractionBHistCarrier
  constructor
  · exact Nonempty.intro cauchyCompletionRetractionChapterTasteGate
  · rfl

end BEDC.Derived.CauchyCompletionRetractionUp

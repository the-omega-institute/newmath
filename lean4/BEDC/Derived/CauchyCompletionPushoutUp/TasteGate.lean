import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionPushoutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionPushoutUp : Type where
  | mk (S L R Q E H C P N : BHist) : CauchyCompletionPushoutUp
  deriving DecidableEq

def cauchyCompletionPushoutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionPushoutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionPushoutEncodeBHist h

def cauchyCompletionPushoutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionPushoutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionPushoutDecodeBHist tail)

private theorem CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionPushoutToEventFlow : CauchyCompletionPushoutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionPushoutUp.mk S L R Q E H C P N =>
      [[BMark.b0],
        cauchyCompletionPushoutEncodeBHist S,
        [BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionPushoutEncodeBHist N]

private def cauchyCompletionPushoutEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionPushoutEventAtDefault index rest

def cauchyCompletionPushoutFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionPushoutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionPushoutUp.mk
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 1 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 3 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 5 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 7 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 9 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 11 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 13 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 15 ef))
      (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEventAtDefault 17 ef)))

private theorem CauchyCompletionPushoutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionPushoutUp,
      cauchyCompletionPushoutFromEventFlow (cauchyCompletionPushoutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L R Q E H C P N =>
      change
        some
          (CauchyCompletionPushoutUp.mk
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist S))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist L))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist R))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist Q))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist E))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist H))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist C))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist P))
            (cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist N))) =
          some (CauchyCompletionPushoutUp.mk S L R Q E H C P N)
      rw [CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode L,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionPushoutTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionPushoutUp} :
    cauchyCompletionPushoutToEventFlow x = cauchyCompletionPushoutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionPushoutFromEventFlow (cauchyCompletionPushoutToEventFlow x) =
        cauchyCompletionPushoutFromEventFlow (cauchyCompletionPushoutToEventFlow y) :=
    congrArg cauchyCompletionPushoutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionPushoutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCompletionPushoutTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionPushoutBHistCarrier :
    BHistCarrier CauchyCompletionPushoutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionPushoutToEventFlow
  fromEventFlow := cauchyCompletionPushoutFromEventFlow

instance cauchyCompletionPushoutChapterTasteGate :
    ChapterTasteGate CauchyCompletionPushoutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionPushoutFromEventFlow (cauchyCompletionPushoutToEventFlow x) = some x
    exact CauchyCompletionPushoutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionPushoutTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionPushoutTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionPushoutDecodeBHist (cauchyCompletionPushoutEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionPushoutUp,
        cauchyCompletionPushoutFromEventFlow (cauchyCompletionPushoutToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionPushoutUp,
          cauchyCompletionPushoutToEventFlow x = cauchyCompletionPushoutToEventFlow y →
            x = y) ∧
          cauchyCompletionPushoutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionPushoutTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionPushoutTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionPushoutTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionPushoutUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AiryFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AiryFunctionUp : Type where
  | mk (D I K T S R E H C P N : BHist) : AiryFunctionUp
  deriving DecidableEq

def airyFunctionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: airyFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: airyFunctionEncodeBHist h

def airyFunctionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (airyFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (airyFunctionDecodeBHist tail)

private theorem AiryFunctionTasteGate_single_carrier_alignment_decode :
    forall h : BHist, airyFunctionDecodeBHist (airyFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def airyFunctionToEventFlow : AiryFunctionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AiryFunctionUp.mk D I K T S R E H C P N =>
      [[BMark.b0],
        airyFunctionEncodeBHist D,
        [BMark.b1, BMark.b0],
        airyFunctionEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        airyFunctionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        airyFunctionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        airyFunctionEncodeBHist N]

private def airyFunctionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => airyFunctionEventAtDefault index rest

def airyFunctionFromEventFlow (ef : EventFlow) : Option AiryFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AiryFunctionUp.mk
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 1 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 3 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 5 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 7 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 9 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 11 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 13 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 15 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 17 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 19 ef))
      (airyFunctionDecodeBHist (airyFunctionEventAtDefault 21 ef)))

private theorem AiryFunctionTasteGate_single_carrier_alignment_round_trip :
    forall x : AiryFunctionUp,
      airyFunctionFromEventFlow (airyFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D I K T S R E H C P N =>
      change
        some
          (AiryFunctionUp.mk
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist D))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist I))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist K))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist T))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist S))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist R))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist E))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist H))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist C))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist P))
            (airyFunctionDecodeBHist (airyFunctionEncodeBHist N))) =
          some (AiryFunctionUp.mk D I K T S R E H C P N)
      rw [AiryFunctionTasteGate_single_carrier_alignment_decode D,
        AiryFunctionTasteGate_single_carrier_alignment_decode I,
        AiryFunctionTasteGate_single_carrier_alignment_decode K,
        AiryFunctionTasteGate_single_carrier_alignment_decode T,
        AiryFunctionTasteGate_single_carrier_alignment_decode S,
        AiryFunctionTasteGate_single_carrier_alignment_decode R,
        AiryFunctionTasteGate_single_carrier_alignment_decode E,
        AiryFunctionTasteGate_single_carrier_alignment_decode H,
        AiryFunctionTasteGate_single_carrier_alignment_decode C,
        AiryFunctionTasteGate_single_carrier_alignment_decode P,
        AiryFunctionTasteGate_single_carrier_alignment_decode N]

private theorem AiryFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AiryFunctionUp} :
    airyFunctionToEventFlow x = airyFunctionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      airyFunctionFromEventFlow (airyFunctionToEventFlow x) =
        airyFunctionFromEventFlow (airyFunctionToEventFlow y) :=
    congrArg airyFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AiryFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AiryFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance airyFunctionBHistCarrier : BHistCarrier AiryFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := airyFunctionToEventFlow
  fromEventFlow := airyFunctionFromEventFlow

instance airyFunctionChapterTasteGate : ChapterTasteGate AiryFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change airyFunctionFromEventFlow (airyFunctionToEventFlow x) = some x
    exact AiryFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AiryFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate AiryFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  airyFunctionChapterTasteGate

theorem AiryFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, airyFunctionDecodeBHist (airyFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AiryFunctionUp) ∧
        Nonempty (ChapterTasteGate AiryFunctionUp) ∧
          airyFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AiryFunctionTasteGate_single_carrier_alignment_decode,
      ⟨airyFunctionBHistCarrier⟩,
      ⟨airyFunctionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.AiryFunctionUp

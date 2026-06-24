import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceCompleteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceCompleteUp : Type where
  | mk (S M R E Q H C P N : BHist) : CauchySequenceCompleteUp
  deriving DecidableEq

def cauchySequenceCompleteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceCompleteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceCompleteEncodeBHist h

def cauchySequenceCompleteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceCompleteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceCompleteDecodeBHist tail)

private theorem CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceCompleteToEventFlow : CauchySequenceCompleteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceCompleteUp.mk S M R E Q H C P N =>
      [cauchySequenceCompleteEncodeBHist S,
        cauchySequenceCompleteEncodeBHist M,
        cauchySequenceCompleteEncodeBHist R,
        cauchySequenceCompleteEncodeBHist E,
        cauchySequenceCompleteEncodeBHist Q,
        cauchySequenceCompleteEncodeBHist H,
        cauchySequenceCompleteEncodeBHist C,
        cauchySequenceCompleteEncodeBHist P,
        cauchySequenceCompleteEncodeBHist N]

def cauchySequenceCompleteFromEventFlow : EventFlow → Option CauchySequenceCompleteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
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
                                          some
                                            (CauchySequenceCompleteUp.mk
                                              (cauchySequenceCompleteDecodeBHist S)
                                              (cauchySequenceCompleteDecodeBHist M)
                                              (cauchySequenceCompleteDecodeBHist R)
                                              (cauchySequenceCompleteDecodeBHist E)
                                              (cauchySequenceCompleteDecodeBHist Q)
                                              (cauchySequenceCompleteDecodeBHist H)
                                              (cauchySequenceCompleteDecodeBHist C)
                                              (cauchySequenceCompleteDecodeBHist P)
                                              (cauchySequenceCompleteDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchySequenceCompleteTasteGate_single_carrier_alignment_round_trip
    (x : CauchySequenceCompleteUp) :
    cauchySequenceCompleteFromEventFlow (cauchySequenceCompleteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M R E Q H C P N =>
      change
        some
          (CauchySequenceCompleteUp.mk
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist S))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist M))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist R))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist E))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist Q))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist H))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist C))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist P))
            (cauchySequenceCompleteDecodeBHist (cauchySequenceCompleteEncodeBHist N))) =
          some (CauchySequenceCompleteUp.mk S M R E Q H C P N)
      rw [CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode S,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode M,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode R,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode E,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode Q,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode H,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode C,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode P,
        CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySequenceCompleteTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceCompleteUp} :
    cauchySequenceCompleteToEventFlow x = cauchySequenceCompleteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceCompleteFromEventFlow (cauchySequenceCompleteToEventFlow x) =
        cauchySequenceCompleteFromEventFlow (cauchySequenceCompleteToEventFlow y) :=
    congrArg cauchySequenceCompleteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySequenceCompleteTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequenceCompleteTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySequenceCompleteBHistCarrier : BHistCarrier CauchySequenceCompleteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceCompleteToEventFlow
  fromEventFlow := cauchySequenceCompleteFromEventFlow

instance cauchySequenceCompleteChapterTasteGate :
    ChapterTasteGate CauchySequenceCompleteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceCompleteFromEventFlow (cauchySequenceCompleteToEventFlow x) = some x
    exact CauchySequenceCompleteTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySequenceCompleteTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchySequenceCompleteTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchySequenceCompleteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceCompleteChapterTasteGate

theorem CauchySequenceCompleteTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySequenceCompleteDecodeBHist
      (cauchySequenceCompleteEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchySequenceCompleteUp) ∧
        Nonempty (ChapterTasteGate CauchySequenceCompleteUp) ∧
          cauchySequenceCompleteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySequenceCompleteTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchySequenceCompleteBHistCarrier⟩,
      ⟨cauchySequenceCompleteChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchySequenceCompleteUp

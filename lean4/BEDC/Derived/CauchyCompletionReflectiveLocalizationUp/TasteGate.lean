import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectiveLocalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectiveLocalizationUp : Type where
  | mk (S Q I U F K T H C P N : BHist) : CauchyCompletionReflectiveLocalizationUp
  deriving DecidableEq

def CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist h

def CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
          tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
          tail)

private theorem
    CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
          h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectiveLocalizationFields :
    CauchyCompletionReflectiveLocalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectiveLocalizationUp.mk S Q I U F K T H C P N =>
      [S, Q, I, U, F, K, T, H, C, P, N]

def cauchyCompletionReflectiveLocalizationToEventFlow :
    CauchyCompletionReflectiveLocalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionReflectiveLocalizationFields x).map
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist

private def cauchyCompletionReflectiveLocalizationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectiveLocalizationEventAt index rest

def cauchyCompletionReflectiveLocalizationFromEventFlow (ef : EventFlow) :
    Option CauchyCompletionReflectiveLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionReflectiveLocalizationUp.mk
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 0 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 1 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 2 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 3 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 4 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 5 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 6 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 7 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 8 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 9 ef))
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (cauchyCompletionReflectiveLocalizationEventAt 10 ef)))

private theorem
    CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionReflectiveLocalizationUp) :
    cauchyCompletionReflectiveLocalizationFromEventFlow
      (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S Q I U F K T H C P N =>
      change
        some
          (CauchyCompletionReflectiveLocalizationUp.mk
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                S))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                Q))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                I))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                U))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                F))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                K))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                T))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                H))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                C))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                P))
            (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
                N))) =
          some (CauchyCompletionReflectiveLocalizationUp.mk S Q I U F K T H C P N)
      rw [
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode I,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode F,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode K,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode T,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionReflectiveLocalizationUp} :
    cauchyCompletionReflectiveLocalizationToEventFlow x =
        cauchyCompletionReflectiveLocalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectiveLocalizationFromEventFlow
          (cauchyCompletionReflectiveLocalizationToEventFlow x) =
        cauchyCompletionReflectiveLocalizationFromEventFlow
          (cauchyCompletionReflectiveLocalizationToEventFlow y) :=
    congrArg cauchyCompletionReflectiveLocalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip
        x).symm
      (Eq.trans hread
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionReflectiveLocalizationBHistCarrier :
    BHistCarrier CauchyCompletionReflectiveLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectiveLocalizationToEventFlow
  fromEventFlow := cauchyCompletionReflectiveLocalizationFromEventFlow

instance cauchyCompletionReflectiveLocalizationChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectiveLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectiveLocalizationFromEventFlow
        (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x
    exact CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCompletionReflectiveLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectiveLocalizationChapterTasteGate

theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      (∀ x : CauchyCompletionReflectiveLocalizationUp,
        cauchyCompletionReflectiveLocalizationFromEventFlow
          (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionReflectiveLocalizationUp,
          cauchyCompletionReflectiveLocalizationToEventFlow x =
              cauchyCompletionReflectiveLocalizationToEventFlow y → x = y) ∧
          CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_encodeBHist
              BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectiveLocalizationUp

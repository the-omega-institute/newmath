import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealOrderUp : Type where
  | mk (S T W D Q R A H C P N : BHist) : CauchyRealOrderUp
  deriving DecidableEq

def cauchyRealOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealOrderEncodeBHist h

def cauchyRealOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealOrderDecodeBHist tail)

private theorem CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealOrderToEventFlow : CauchyRealOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealOrderUp.mk S T W D Q R A H C P N =>
      [cauchyRealOrderEncodeBHist S, cauchyRealOrderEncodeBHist T,
        cauchyRealOrderEncodeBHist W, cauchyRealOrderEncodeBHist D,
        cauchyRealOrderEncodeBHist Q, cauchyRealOrderEncodeBHist R,
        cauchyRealOrderEncodeBHist A, cauchyRealOrderEncodeBHist H,
        cauchyRealOrderEncodeBHist C, cauchyRealOrderEncodeBHist P,
        cauchyRealOrderEncodeBHist N]

def cauchyRealOrderFromEventFlow : EventFlow → Option CauchyRealOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: rest =>
      match rest with
      | [] => none
      | T :: rest =>
          match rest with
          | [] => none
          | W :: rest =>
              match rest with
              | [] => none
              | D :: rest =>
                  match rest with
                  | [] => none
                  | Q :: rest =>
                      match rest with
                      | [] => none
                      | R :: rest =>
                          match rest with
                          | [] => none
                          | A :: rest =>
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
                                                    (CauchyRealOrderUp.mk
                                                      (cauchyRealOrderDecodeBHist S)
                                                      (cauchyRealOrderDecodeBHist T)
                                                      (cauchyRealOrderDecodeBHist W)
                                                      (cauchyRealOrderDecodeBHist D)
                                                      (cauchyRealOrderDecodeBHist Q)
                                                      (cauchyRealOrderDecodeBHist R)
                                                      (cauchyRealOrderDecodeBHist A)
                                                      (cauchyRealOrderDecodeBHist H)
                                                      (cauchyRealOrderDecodeBHist C)
                                                      (cauchyRealOrderDecodeBHist P)
                                                      (cauchyRealOrderDecodeBHist N))
                                              | _ :: _ => none
  | [] => none

private theorem CauchyRealOrderUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealOrderUp,
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W D Q R A H C P N =>
      change
        some
          (CauchyRealOrderUp.mk
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist S))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist T))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist W))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist D))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist Q))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist R))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist A))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist H))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist C))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist P))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist N))) =
          some (CauchyRealOrderUp.mk S T W D Q R A H C P N)
      rw [CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode T,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode W,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode A,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealOrderUp} :
    cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) =
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow y) :=
    congrArg cauchyRealOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealOrderUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealOrderUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRealOrderBHistCarrier : BHistCarrier CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealOrderToEventFlow
  fromEventFlow := cauchyRealOrderFromEventFlow

instance cauchyRealOrderChapterTasteGate : ChapterTasteGate CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x
    exact CauchyRealOrderUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRealOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealOrderChapterTasteGate

theorem CauchyRealOrderUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h) ∧
      (∀ x : CauchyRealOrderUp,
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x) ∧
      (∀ x y : CauchyRealOrderUp,
        cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y → x = y) ∧
      cauchyRealOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyRealOrderUpTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealOrderUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => CauchyRealOrderUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyRealOrderUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealOrderUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealOrderUp : Type where
  | mk :
      (sourceLeft sourceRight window dyadic quotient realSeal verdict transport replay
        provenance localName : BHist) ->
        CauchyRealOrderUp
  deriving DecidableEq

def cauchyRealOrderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealOrderEncodeBHist h

def cauchyRealOrderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealOrderDecodeBHist tail)

theorem CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRealOrderFields : CauchyRealOrderUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealOrderUp.mk sourceLeft sourceRight window dyadic quotient realSeal verdict
      transport replay provenance localName =>
      [sourceLeft, sourceRight, window, dyadic, quotient, realSeal, verdict, transport, replay,
        provenance, localName]

def cauchyRealOrderToEventFlow : CauchyRealOrderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealOrderFields x).map cauchyRealOrderEncodeBHist

def cauchyRealOrderFromEventFlow : EventFlow -> Option CauchyRealOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceLeft :: rest0 =>
      match rest0 with
      | [] => none
      | sourceRight :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | quotient :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | verdict :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyRealOrderUp.mk
                                                      (cauchyRealOrderDecodeBHist sourceLeft)
                                                      (cauchyRealOrderDecodeBHist sourceRight)
                                                      (cauchyRealOrderDecodeBHist window)
                                                      (cauchyRealOrderDecodeBHist dyadic)
                                                      (cauchyRealOrderDecodeBHist quotient)
                                                      (cauchyRealOrderDecodeBHist realSeal)
                                                      (cauchyRealOrderDecodeBHist verdict)
                                                      (cauchyRealOrderDecodeBHist transport)
                                                      (cauchyRealOrderDecodeBHist replay)
                                                      (cauchyRealOrderDecodeBHist provenance)
                                                      (cauchyRealOrderDecodeBHist localName))
                                              | _ :: _ => none

theorem CauchyRealOrderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRealOrderUp,
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight window dyadic quotient realSeal verdict transport replay
      provenance localName =>
      change
        some
          (CauchyRealOrderUp.mk
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist sourceLeft))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist sourceRight))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist window))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist dyadic))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist quotient))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist realSeal))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist verdict))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist transport))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist replay))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist provenance))
            (cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist localName))) =
          some
            (CauchyRealOrderUp.mk sourceLeft sourceRight window dyadic quotient realSeal
              verdict transport replay provenance localName)
      rw [CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode sourceRight,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode window,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode dyadic,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode quotient,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode verdict,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode localName]

theorem CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealOrderUp} :
    cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) =
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow y) :=
    congrArg cauchyRealOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchyRealOrderTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyRealOrderUp, cauchyRealOrderFields x = cauchyRealOrderFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceLeft1 sourceRight1 window1 dyadic1 quotient1 realSeal1 verdict1 transport1
      replay1 provenance1 localName1 =>
      cases y with
      | mk sourceLeft2 sourceRight2 window2 dyadic2 quotient2 realSeal2 verdict2 transport2
          replay2 provenance2 localName2 =>
          cases hfields
          rfl

instance cauchyRealOrderBHistCarrier : BHistCarrier CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealOrderToEventFlow
  fromEventFlow := cauchyRealOrderFromEventFlow

instance cauchyRealOrderChapterTasteGate : ChapterTasteGate CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyRealOrderTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealOrderFieldFaithful : FieldFaithful CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealOrderFields
  field_faithful := CauchyRealOrderTasteGate_single_carrier_alignment_field_faithful

instance cauchyRealOrderNontrivial : Nontrivial CauchyRealOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRealOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealOrderChapterTasteGate

theorem CauchyRealOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealOrderDecodeBHist (cauchyRealOrderEncodeBHist h) = h) ∧
      (∀ x : CauchyRealOrderUp,
        cauchyRealOrderFromEventFlow (cauchyRealOrderToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealOrderUp,
          cauchyRealOrderToEventFlow x = cauchyRealOrderToEventFlow y -> x = y) ∧
          cauchyRealOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyRealOrderTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchyRealOrderTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyRealOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyRealOrderUp.TasteGate

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow

theorem CauchyRealOrderTasteGate_e0_row_round_trip
    (S T W D Q R A H C P N : BHist) :
    TasteGate.cauchyRealOrderFromEventFlow
      (TasteGate.cauchyRealOrderToEventFlow
        (TasteGate.CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N)) =
      some (TasteGate.CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact TasteGate.CauchyRealOrderTasteGate_single_carrier_alignment_round_trip
    (TasteGate.CauchyRealOrderUp.mk (BHist.e0 S) T W D Q R A H C P N)

end BEDC.Derived.CauchyRealOrderUp

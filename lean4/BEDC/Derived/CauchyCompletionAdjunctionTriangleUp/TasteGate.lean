import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionAdjunctionTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionAdjunctionTriangleUp : Type where
  | mk (F A U I R W D E H C P N : BHist) :
      CauchyCompletionAdjunctionTriangleUp
  deriving DecidableEq

def cauchyCompletionAdjunctionTriangleEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionAdjunctionTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionAdjunctionTriangleEncodeBHist h

def cauchyCompletionAdjunctionTriangleDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionAdjunctionTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionAdjunctionTriangleDecodeBHist tail)

private theorem CauchyCompletionAdjunctionTriangleTasteGate_decode_encode :
    forall h : BHist,
      cauchyCompletionAdjunctionTriangleDecodeBHist
        (cauchyCompletionAdjunctionTriangleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionAdjunctionTriangleFields :
    CauchyCompletionAdjunctionTriangleUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionAdjunctionTriangleUp.mk F A U I R W D E H C P N =>
      [F, A, U, I, R, W, D, E, H, C, P, N]

def cauchyCompletionAdjunctionTriangleToEventFlow :
    CauchyCompletionAdjunctionTriangleUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionAdjunctionTriangleFields x).map
      cauchyCompletionAdjunctionTriangleEncodeBHist

private def cauchyCompletionAdjunctionTriangleDecodePacket
    (F A U I R W D E H C P N : RawEvent) : CauchyCompletionAdjunctionTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyCompletionAdjunctionTriangleUp.mk
    (cauchyCompletionAdjunctionTriangleDecodeBHist F)
    (cauchyCompletionAdjunctionTriangleDecodeBHist A)
    (cauchyCompletionAdjunctionTriangleDecodeBHist U)
    (cauchyCompletionAdjunctionTriangleDecodeBHist I)
    (cauchyCompletionAdjunctionTriangleDecodeBHist R)
    (cauchyCompletionAdjunctionTriangleDecodeBHist W)
    (cauchyCompletionAdjunctionTriangleDecodeBHist D)
    (cauchyCompletionAdjunctionTriangleDecodeBHist E)
    (cauchyCompletionAdjunctionTriangleDecodeBHist H)
    (cauchyCompletionAdjunctionTriangleDecodeBHist C)
    (cauchyCompletionAdjunctionTriangleDecodeBHist P)
    (cauchyCompletionAdjunctionTriangleDecodeBHist N)

def cauchyCompletionAdjunctionTriangleFromEventFlow :
    EventFlow -> Option CauchyCompletionAdjunctionTriangleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (cauchyCompletionAdjunctionTriangleDecodePacket
                                                          F A U I R W D E H C P N)
                                                  | _ :: _ => none

private theorem CauchyCompletionAdjunctionTriangleTasteGate_round_trip :
    forall x : CauchyCompletionAdjunctionTriangleUp,
      cauchyCompletionAdjunctionTriangleFromEventFlow
        (cauchyCompletionAdjunctionTriangleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A U I R W D E H C P N =>
      change
        some
          (cauchyCompletionAdjunctionTriangleDecodePacket
            (cauchyCompletionAdjunctionTriangleEncodeBHist F)
            (cauchyCompletionAdjunctionTriangleEncodeBHist A)
            (cauchyCompletionAdjunctionTriangleEncodeBHist U)
            (cauchyCompletionAdjunctionTriangleEncodeBHist I)
            (cauchyCompletionAdjunctionTriangleEncodeBHist R)
            (cauchyCompletionAdjunctionTriangleEncodeBHist W)
            (cauchyCompletionAdjunctionTriangleEncodeBHist D)
            (cauchyCompletionAdjunctionTriangleEncodeBHist E)
            (cauchyCompletionAdjunctionTriangleEncodeBHist H)
            (cauchyCompletionAdjunctionTriangleEncodeBHist C)
            (cauchyCompletionAdjunctionTriangleEncodeBHist P)
            (cauchyCompletionAdjunctionTriangleEncodeBHist N)) =
          some (CauchyCompletionAdjunctionTriangleUp.mk F A U I R W D E H C P N)
      unfold cauchyCompletionAdjunctionTriangleDecodePacket
      rw [CauchyCompletionAdjunctionTriangleTasteGate_decode_encode F,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode A,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode U,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode I,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode R,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode W,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode D,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode E,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode H,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode C,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode P,
        CauchyCompletionAdjunctionTriangleTasteGate_decode_encode N]


private theorem CauchyCompletionAdjunctionTriangleTasteGate_toEventFlow_injective
    {x y : CauchyCompletionAdjunctionTriangleUp} :
    cauchyCompletionAdjunctionTriangleToEventFlow x =
        cauchyCompletionAdjunctionTriangleToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) =
        cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow y) :=
    congrArg cauchyCompletionAdjunctionTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionAdjunctionTriangleTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyCompletionAdjunctionTriangleTasteGate_round_trip y)))

private theorem CauchyCompletionAdjunctionTriangleTasteGate_field_faithful :
    forall x y : CauchyCompletionAdjunctionTriangleUp,
      cauchyCompletionAdjunctionTriangleFields x =
          cauchyCompletionAdjunctionTriangleFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 A1 U1 I1 R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 A2 U2 I2 R2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionAdjunctionTriangleBHistCarrier :
    BHistCarrier CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionAdjunctionTriangleToEventFlow
  fromEventFlow := cauchyCompletionAdjunctionTriangleFromEventFlow

instance cauchyCompletionAdjunctionTriangleChapterTasteGate :
    ChapterTasteGate CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) = some x
    exact CauchyCompletionAdjunctionTriangleTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionAdjunctionTriangleTasteGate_toEventFlow_injective heq)

instance cauchyCompletionAdjunctionTriangleFieldFaithful :
    FieldFaithful CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionAdjunctionTriangleFields
  field_faithful := CauchyCompletionAdjunctionTriangleTasteGate_field_faithful

instance cauchyCompletionAdjunctionTriangleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionAdjunctionTriangleUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionAdjunctionTriangleUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def cauchyCompletionAdjunctionTriangleTasteGate :
    ChapterTasteGate CauchyCompletionAdjunctionTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionAdjunctionTriangleChapterTasteGate

theorem CauchyCompletionAdjunctionTriangleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionAdjunctionTriangleDecodeBHist
        (cauchyCompletionAdjunctionTriangleEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionAdjunctionTriangleUp,
        cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionAdjunctionTriangleUp,
          cauchyCompletionAdjunctionTriangleToEventFlow x =
              cauchyCompletionAdjunctionTriangleToEventFlow y ->
            x = y) ∧
          cauchyCompletionAdjunctionTriangleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCompletionAdjunctionTriangleTasteGate_decode_encode
  · constructor
    · exact CauchyCompletionAdjunctionTriangleTasteGate_round_trip
    · constructor
      · intro x y heq
        exact CauchyCompletionAdjunctionTriangleTasteGate_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCompletionAdjunctionTriangleUp

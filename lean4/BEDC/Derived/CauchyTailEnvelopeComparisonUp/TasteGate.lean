import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEnvelopeComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEnvelopeComparisonUp : Type where
  | mk (E0 E1 W0 W1 D J T H C P N : BHist) : CauchyTailEnvelopeComparisonUp

def cauchyTailEnvelopeComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEnvelopeComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEnvelopeComparisonEncodeBHist h

def cauchyTailEnvelopeComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEnvelopeComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEnvelopeComparisonDecodeBHist tail)

private theorem cauchyTailEnvelopeComparison_decode_encode_bhist :
    ∀ h : BHist,
      cauchyTailEnvelopeComparisonDecodeBHist
        (cauchyTailEnvelopeComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyTailEnvelopeComparison_mk_congr
    {E0 E0' E1 E1' W0 W0' W1 W1' D D' J J' T T' H H' C C' P P' N N' :
      BHist}
    (hE0 : E0' = E0) (hE1 : E1' = E1) (hW0 : W0' = W0)
    (hW1 : W1' = W1) (hD : D' = D) (hJ : J' = J) (hT : T' = T)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyTailEnvelopeComparisonUp.mk E0' E1' W0' W1' D' J' T' H' C' P' N' =
      CauchyTailEnvelopeComparisonUp.mk E0 E1 W0 W1 D J T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hE0
  cases hE1
  cases hW0
  cases hW1
  cases hD
  cases hJ
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyTailEnvelopeComparisonFields :
    CauchyTailEnvelopeComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEnvelopeComparisonUp.mk E0 E1 W0 W1 D J T H C P N =>
      [E0, E1, W0, W1, D, J, T, H, C, P, N]

def cauchyTailEnvelopeComparisonToEventFlow :
    CauchyTailEnvelopeComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEnvelopeComparisonUp.mk E0 E1 W0 W1 D J T H C P N =>
      [cauchyTailEnvelopeComparisonEncodeBHist E0,
        cauchyTailEnvelopeComparisonEncodeBHist E1,
        cauchyTailEnvelopeComparisonEncodeBHist W0,
        cauchyTailEnvelopeComparisonEncodeBHist W1,
        cauchyTailEnvelopeComparisonEncodeBHist D,
        cauchyTailEnvelopeComparisonEncodeBHist J,
        cauchyTailEnvelopeComparisonEncodeBHist T,
        cauchyTailEnvelopeComparisonEncodeBHist H,
        cauchyTailEnvelopeComparisonEncodeBHist C,
        cauchyTailEnvelopeComparisonEncodeBHist P,
        cauchyTailEnvelopeComparisonEncodeBHist N]

def cauchyTailEnvelopeComparisonFromEventFlow :
    EventFlow → Option CauchyTailEnvelopeComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | E0 :: restE0 =>
      match restE0 with
      | E1 :: restE1 =>
          match restE1 with
          | W0 :: restW0 =>
              match restW0 with
              | W1 :: restW1 =>
                  match restW1 with
                  | D :: restD =>
                      match restD with
                      | J :: restJ =>
                          match restJ with
                          | T :: restT =>
                              match restT with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (CauchyTailEnvelopeComparisonUp.mk
                                                      (cauchyTailEnvelopeComparisonDecodeBHist E0)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist E1)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist W0)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist W1)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist D)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist J)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist T)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist H)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist C)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist P)
                                                      (cauchyTailEnvelopeComparisonDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyTailEnvelopeComparison_round_trip :
    ∀ x : CauchyTailEnvelopeComparisonUp,
      cauchyTailEnvelopeComparisonFromEventFlow
        (cauchyTailEnvelopeComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E0 E1 W0 W1 D J T H C P N =>
      change
        some
          (CauchyTailEnvelopeComparisonUp.mk
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist E0))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist E1))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist W0))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist W1))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist D))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist J))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist T))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist H))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist C))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist P))
            (cauchyTailEnvelopeComparisonDecodeBHist
              (cauchyTailEnvelopeComparisonEncodeBHist N))) =
          some (CauchyTailEnvelopeComparisonUp.mk E0 E1 W0 W1 D J T H C P N)
      exact
        congrArg some
          (cauchyTailEnvelopeComparison_mk_congr
            (cauchyTailEnvelopeComparison_decode_encode_bhist E0)
            (cauchyTailEnvelopeComparison_decode_encode_bhist E1)
            (cauchyTailEnvelopeComparison_decode_encode_bhist W0)
            (cauchyTailEnvelopeComparison_decode_encode_bhist W1)
            (cauchyTailEnvelopeComparison_decode_encode_bhist D)
            (cauchyTailEnvelopeComparison_decode_encode_bhist J)
            (cauchyTailEnvelopeComparison_decode_encode_bhist T)
            (cauchyTailEnvelopeComparison_decode_encode_bhist H)
            (cauchyTailEnvelopeComparison_decode_encode_bhist C)
            (cauchyTailEnvelopeComparison_decode_encode_bhist P)
            (cauchyTailEnvelopeComparison_decode_encode_bhist N))

private theorem cauchyTailEnvelopeComparisonToEventFlow_injective
    {x y : CauchyTailEnvelopeComparisonUp} :
    cauchyTailEnvelopeComparisonToEventFlow x =
      cauchyTailEnvelopeComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEnvelopeComparisonFromEventFlow
          (cauchyTailEnvelopeComparisonToEventFlow x) =
        cauchyTailEnvelopeComparisonFromEventFlow
          (cauchyTailEnvelopeComparisonToEventFlow y) :=
    congrArg cauchyTailEnvelopeComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailEnvelopeComparison_round_trip x).symm
      (Eq.trans hread (cauchyTailEnvelopeComparison_round_trip y)))

instance cauchyTailEnvelopeComparisonBHistCarrier :
    BHistCarrier CauchyTailEnvelopeComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEnvelopeComparisonToEventFlow
  fromEventFlow := cauchyTailEnvelopeComparisonFromEventFlow

instance cauchyTailEnvelopeComparisonChapterTasteGate :
    ChapterTasteGate CauchyTailEnvelopeComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyTailEnvelopeComparisonFromEventFlow
        (cauchyTailEnvelopeComparisonToEventFlow x) = some x
    exact cauchyTailEnvelopeComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailEnvelopeComparisonToEventFlow_injective heq)

theorem CauchyTailEnvelopeComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailEnvelopeComparisonDecodeBHist
        (cauchyTailEnvelopeComparisonEncodeBHist h) = h) ∧
      (∀ x : CauchyTailEnvelopeComparisonUp,
        cauchyTailEnvelopeComparisonFromEventFlow
          (cauchyTailEnvelopeComparisonToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailEnvelopeComparisonUp,
          cauchyTailEnvelopeComparisonToEventFlow x =
            cauchyTailEnvelopeComparisonToEventFlow y → x = y) ∧
          cauchyTailEnvelopeComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyTailEnvelopeComparison_decode_encode_bhist
  · constructor
    · exact cauchyTailEnvelopeComparison_round_trip
    · constructor
      · intro x y heq
        exact cauchyTailEnvelopeComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyTailEnvelopeComparisonUp

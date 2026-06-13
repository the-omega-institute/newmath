import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalEndpointAmbiguityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalEndpointAmbiguityUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (D E S M Q R Y H C P N : BHist) →
        DecimalEndpointAmbiguityUp
  deriving DecidableEq

def decimalEndpointAmbiguityTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1, BMark.b0]

def decimalEndpointAmbiguityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalEndpointAmbiguityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalEndpointAmbiguityEncodeBHist h

def decimalEndpointAmbiguityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalEndpointAmbiguityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalEndpointAmbiguityDecodeBHist tail)

private theorem decimalEndpointAmbiguityDecodeEncode :
    ∀ h : BHist,
      decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decimalEndpointAmbiguityFields :
    DecimalEndpointAmbiguityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalEndpointAmbiguityUp.mk D E S M Q R Y H C P N =>
      [D, E, S, M, Q, R, Y, H, C, P, N]

def decimalEndpointAmbiguityToEventFlow :
    DecimalEndpointAmbiguityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalEndpointAmbiguityUp.mk D E S M Q R Y H C P N =>
      [decimalEndpointAmbiguityTag,
        decimalEndpointAmbiguityEncodeBHist D,
        decimalEndpointAmbiguityEncodeBHist E,
        decimalEndpointAmbiguityEncodeBHist S,
        decimalEndpointAmbiguityEncodeBHist M,
        decimalEndpointAmbiguityEncodeBHist Q,
        decimalEndpointAmbiguityEncodeBHist R,
        decimalEndpointAmbiguityEncodeBHist Y,
        decimalEndpointAmbiguityEncodeBHist H,
        decimalEndpointAmbiguityEncodeBHist C,
        decimalEndpointAmbiguityEncodeBHist P,
        decimalEndpointAmbiguityEncodeBHist N]

def decimalEndpointAmbiguityFromEventFlow :
    EventFlow → Option DecimalEndpointAmbiguityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tag :: rest0 =>
      match tag with
      | [BMark.b1, BMark.b0, BMark.b1, BMark.b1, BMark.b0] =>
          match rest0 with
          | [] => none
          | D :: rest1 =>
              match rest1 with
              | [] => none
              | E :: rest2 =>
                  match rest2 with
                  | [] => none
                  | S :: rest3 =>
                      match rest3 with
                      | [] => none
                      | M :: rest4 =>
                          match rest4 with
                          | [] => none
                          | Q :: rest5 =>
                              match rest5 with
                              | [] => none
                              | R :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | Y :: rest7 =>
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
                                                            (DecimalEndpointAmbiguityUp.mk
                                                              (decimalEndpointAmbiguityDecodeBHist D)
                                                              (decimalEndpointAmbiguityDecodeBHist E)
                                                              (decimalEndpointAmbiguityDecodeBHist S)
                                                              (decimalEndpointAmbiguityDecodeBHist M)
                                                              (decimalEndpointAmbiguityDecodeBHist Q)
                                                              (decimalEndpointAmbiguityDecodeBHist R)
                                                              (decimalEndpointAmbiguityDecodeBHist Y)
                                                              (decimalEndpointAmbiguityDecodeBHist H)
                                                              (decimalEndpointAmbiguityDecodeBHist C)
                                                              (decimalEndpointAmbiguityDecodeBHist P)
                                                              (decimalEndpointAmbiguityDecodeBHist N))
                                                      | _ :: _ => none
      | _ => none

private theorem decimalEndpointAmbiguityRoundTrip (x : DecimalEndpointAmbiguityUp) :
    decimalEndpointAmbiguityFromEventFlow (decimalEndpointAmbiguityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D E S M Q R Y H C P N =>
      change
        some
          (DecimalEndpointAmbiguityUp.mk
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist D))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist E))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist S))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist M))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist Q))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist R))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist Y))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist H))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist C))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist P))
            (decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist N))) =
          some (DecimalEndpointAmbiguityUp.mk D E S M Q R Y H C P N)
      rw [decimalEndpointAmbiguityDecodeEncode D, decimalEndpointAmbiguityDecodeEncode E,
        decimalEndpointAmbiguityDecodeEncode S, decimalEndpointAmbiguityDecodeEncode M,
        decimalEndpointAmbiguityDecodeEncode Q, decimalEndpointAmbiguityDecodeEncode R,
        decimalEndpointAmbiguityDecodeEncode Y, decimalEndpointAmbiguityDecodeEncode H,
        decimalEndpointAmbiguityDecodeEncode C, decimalEndpointAmbiguityDecodeEncode P,
        decimalEndpointAmbiguityDecodeEncode N]

private theorem decimalEndpointAmbiguityToEventFlow_injective
    {x y : DecimalEndpointAmbiguityUp} :
    decimalEndpointAmbiguityToEventFlow x = decimalEndpointAmbiguityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalEndpointAmbiguityFromEventFlow (decimalEndpointAmbiguityToEventFlow x) =
        decimalEndpointAmbiguityFromEventFlow (decimalEndpointAmbiguityToEventFlow y) :=
    congrArg decimalEndpointAmbiguityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decimalEndpointAmbiguityRoundTrip x).symm
      (Eq.trans hread (decimalEndpointAmbiguityRoundTrip y)))

instance decimalEndpointAmbiguityBHistCarrier : BHistCarrier DecimalEndpointAmbiguityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalEndpointAmbiguityToEventFlow
  fromEventFlow := decimalEndpointAmbiguityFromEventFlow

instance decimalEndpointAmbiguityChapterTasteGate :
    ChapterTasteGate DecimalEndpointAmbiguityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      decimalEndpointAmbiguityFromEventFlow (decimalEndpointAmbiguityToEventFlow x) =
        some x
    exact decimalEndpointAmbiguityRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decimalEndpointAmbiguityToEventFlow_injective heq)

def decimalEndpointAmbiguityTasteGate : ChapterTasteGate DecimalEndpointAmbiguityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  decimalEndpointAmbiguityChapterTasteGate

theorem DecimalEndpointAmbiguityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      decimalEndpointAmbiguityDecodeBHist (decimalEndpointAmbiguityEncodeBHist h) = h) ∧
      (∀ D E S M Q R Y H C P N : BHist,
        decimalEndpointAmbiguityFields
            (DecimalEndpointAmbiguityUp.mk D E S M Q R Y H C P N) =
          [D, E, S, M, Q, R, Y, H, C, P, N]) ∧
        decimalEndpointAmbiguityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decimalEndpointAmbiguityDecodeEncode
  · constructor
    · intro D E S M Q R Y H C P N
      rfl
    · rfl

end BEDC.Derived.DecimalEndpointAmbiguityUp

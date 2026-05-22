import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyQuotientBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyQuotientBoundaryUp : Type where
  | mk (S Q F D W R E H C P N : BHist) : CauchyQuotientBoundaryUp
  deriving DecidableEq

def cauchyQuotientBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyQuotientBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyQuotientBoundaryEncodeBHist h

def cauchyQuotientBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyQuotientBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyQuotientBoundaryDecodeBHist tail)

private theorem cauchyQuotientBoundary_decode_encode_bhist :
    ∀ h : BHist,
      cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyQuotientBoundaryToEventFlow : CauchyQuotientBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyQuotientBoundaryUp.mk S Q F D W R E H C P N =>
      [cauchyQuotientBoundaryEncodeBHist S,
        cauchyQuotientBoundaryEncodeBHist Q,
        cauchyQuotientBoundaryEncodeBHist F,
        cauchyQuotientBoundaryEncodeBHist D,
        cauchyQuotientBoundaryEncodeBHist W,
        cauchyQuotientBoundaryEncodeBHist R,
        cauchyQuotientBoundaryEncodeBHist E,
        cauchyQuotientBoundaryEncodeBHist H,
        cauchyQuotientBoundaryEncodeBHist C,
        cauchyQuotientBoundaryEncodeBHist P,
        cauchyQuotientBoundaryEncodeBHist N]

def cauchyQuotientBoundaryFromEventFlow :
    EventFlow → Option CauchyQuotientBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | F :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyQuotientBoundaryUp.mk
                                                      (cauchyQuotientBoundaryDecodeBHist S)
                                                      (cauchyQuotientBoundaryDecodeBHist Q)
                                                      (cauchyQuotientBoundaryDecodeBHist F)
                                                      (cauchyQuotientBoundaryDecodeBHist D)
                                                      (cauchyQuotientBoundaryDecodeBHist W)
                                                      (cauchyQuotientBoundaryDecodeBHist R)
                                                      (cauchyQuotientBoundaryDecodeBHist E)
                                                      (cauchyQuotientBoundaryDecodeBHist H)
                                                      (cauchyQuotientBoundaryDecodeBHist C)
                                                      (cauchyQuotientBoundaryDecodeBHist P)
                                                      (cauchyQuotientBoundaryDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyQuotientBoundary_round_trip :
    ∀ x : CauchyQuotientBoundaryUp,
      cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q F D W R E H C P N =>
      change
        some
          (CauchyQuotientBoundaryUp.mk
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist S))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist Q))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist F))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist D))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist W))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist R))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist E))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist H))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist C))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist P))
            (cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist N))) =
          some (CauchyQuotientBoundaryUp.mk S Q F D W R E H C P N)
      rw [cauchyQuotientBoundary_decode_encode_bhist S,
        cauchyQuotientBoundary_decode_encode_bhist Q,
        cauchyQuotientBoundary_decode_encode_bhist F,
        cauchyQuotientBoundary_decode_encode_bhist D,
        cauchyQuotientBoundary_decode_encode_bhist W,
        cauchyQuotientBoundary_decode_encode_bhist R,
        cauchyQuotientBoundary_decode_encode_bhist E,
        cauchyQuotientBoundary_decode_encode_bhist H,
        cauchyQuotientBoundary_decode_encode_bhist C,
        cauchyQuotientBoundary_decode_encode_bhist P,
        cauchyQuotientBoundary_decode_encode_bhist N]

private theorem cauchyQuotientBoundaryToEventFlow_injective
    {x y : CauchyQuotientBoundaryUp} :
    cauchyQuotientBoundaryToEventFlow x = cauchyQuotientBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
        cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow y) :=
    congrArg cauchyQuotientBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyQuotientBoundary_round_trip x).symm
      (Eq.trans hread (cauchyQuotientBoundary_round_trip y)))

instance cauchyQuotientBoundaryBHistCarrier : BHistCarrier CauchyQuotientBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyQuotientBoundaryToEventFlow
  fromEventFlow := cauchyQuotientBoundaryFromEventFlow

instance cauchyQuotientBoundaryChapterTasteGate :
    ChapterTasteGate CauchyQuotientBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) = some x
    exact cauchyQuotientBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyQuotientBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyQuotientBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyQuotientBoundaryChapterTasteGate

theorem CauchyQuotientBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist h) = h) ∧
      (∀ x : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) = some x) ∧
      (∀ x y : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryToEventFlow x = cauchyQuotientBoundaryToEventFlow y → x = y) ∧
      cauchyQuotientBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyQuotientBoundary_decode_encode_bhist, cauchyQuotientBoundary_round_trip,
      fun _ _ heq => cauchyQuotientBoundaryToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CauchyQuotientBoundaryUp

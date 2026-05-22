import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

namespace TasteGate

inductive CauchyDiagonalLimitUp : Type where
  | mk (R B D V E S Q Y T H C P N : BHist) : CauchyDiagonalLimitUp
  deriving DecidableEq

def cauchyDiagonalLimitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalLimitEncodeBHist h

def cauchyDiagonalLimitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalLimitDecodeBHist tail)

private theorem cauchyDiagonalLimit_decode_encode_bhist :
    forall h : BHist, cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyDiagonalLimitFields : CauchyDiagonalLimitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalLimitUp.mk R B D V E S Q Y T H C P N =>
      [R, B, D, V, E, S, Q, Y, T, H, C, P, N]

def cauchyDiagonalLimitToEventFlow : CauchyDiagonalLimitUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyDiagonalLimitEncodeBHist (cauchyDiagonalLimitFields x)

def cauchyDiagonalLimitFromEventFlow : EventFlow -> Option CauchyDiagonalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | V :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Y :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | T :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (CauchyDiagonalLimitUp.mk
                                                              (cauchyDiagonalLimitDecodeBHist R)
                                                              (cauchyDiagonalLimitDecodeBHist B)
                                                              (cauchyDiagonalLimitDecodeBHist D)
                                                              (cauchyDiagonalLimitDecodeBHist V)
                                                              (cauchyDiagonalLimitDecodeBHist E)
                                                              (cauchyDiagonalLimitDecodeBHist S)
                                                              (cauchyDiagonalLimitDecodeBHist Q)
                                                              (cauchyDiagonalLimitDecodeBHist Y)
                                                              (cauchyDiagonalLimitDecodeBHist T)
                                                              (cauchyDiagonalLimitDecodeBHist H)
                                                              (cauchyDiagonalLimitDecodeBHist C)
                                                              (cauchyDiagonalLimitDecodeBHist P)
                                                              (cauchyDiagonalLimitDecodeBHist N))
                                                      | _ :: _ => none

private theorem cauchyDiagonalLimit_round_trip :
    forall x : CauchyDiagonalLimitUp,
      cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R B D V E S Q Y T H C P N =>
      change
        some
          (CauchyDiagonalLimitUp.mk
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist R))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist B))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist D))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist V))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist E))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist S))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist Q))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist Y))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist T))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist H))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist C))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist P))
            (cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist N))) =
          some (CauchyDiagonalLimitUp.mk R B D V E S Q Y T H C P N)
      rw [cauchyDiagonalLimit_decode_encode_bhist R,
        cauchyDiagonalLimit_decode_encode_bhist B,
        cauchyDiagonalLimit_decode_encode_bhist D,
        cauchyDiagonalLimit_decode_encode_bhist V,
        cauchyDiagonalLimit_decode_encode_bhist E,
        cauchyDiagonalLimit_decode_encode_bhist S,
        cauchyDiagonalLimit_decode_encode_bhist Q,
        cauchyDiagonalLimit_decode_encode_bhist Y,
        cauchyDiagonalLimit_decode_encode_bhist T,
        cauchyDiagonalLimit_decode_encode_bhist H,
        cauchyDiagonalLimit_decode_encode_bhist C,
        cauchyDiagonalLimit_decode_encode_bhist P,
        cauchyDiagonalLimit_decode_encode_bhist N]

private theorem cauchyDiagonalLimitToEventFlow_injective {x y : CauchyDiagonalLimitUp} :
    cauchyDiagonalLimitToEventFlow x = cauchyDiagonalLimitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) =
        cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow y) :=
    congrArg cauchyDiagonalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDiagonalLimit_round_trip x).symm
      (Eq.trans hread (cauchyDiagonalLimit_round_trip y)))

instance cauchyDiagonalLimitBHistCarrier : BHistCarrier CauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalLimitToEventFlow
  fromEventFlow := cauchyDiagonalLimitFromEventFlow

instance cauchyDiagonalLimitChapterTasteGate : ChapterTasteGate CauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x
    exact cauchyDiagonalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDiagonalLimitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyDiagonalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDiagonalLimitChapterTasteGate

theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist h) = h) ∧
      (forall x : CauchyDiagonalLimitUp,
        cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x) ∧
        (forall x y : CauchyDiagonalLimitUp,
          cauchyDiagonalLimitToEventFlow x = cauchyDiagonalLimitToEventFlow y -> x = y) ∧
          cauchyDiagonalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyDiagonalLimit_decode_encode_bhist,
      cauchyDiagonalLimit_round_trip,
      (fun _ _ heq => cauchyDiagonalLimitToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.CauchyDiagonalLimitUp

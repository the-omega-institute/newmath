import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionContinuationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionContinuationUp : Type where
  | mk (Q B S W D R E H C P N : BHist) : CauchyCompletionContinuationUp
  deriving DecidableEq

def cauchyCompletionContinuationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionContinuationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionContinuationEncodeBHist h

def cauchyCompletionContinuationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionContinuationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionContinuationDecodeBHist tail)

private theorem cauchyCompletionContinuation_decode_encode_bhist :
    forall h : BHist,
      cauchyCompletionContinuationDecodeBHist
        (cauchyCompletionContinuationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyCompletionContinuationEncodeBHist_injective {h k : BHist} :
    cauchyCompletionContinuationEncodeBHist h =
        cauchyCompletionContinuationEncodeBHist k ->
      h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionContinuationDecodeBHist
          (cauchyCompletionContinuationEncodeBHist h) =
        cauchyCompletionContinuationDecodeBHist
          (cauchyCompletionContinuationEncodeBHist k) :=
    congrArg cauchyCompletionContinuationDecodeBHist heq
  exact
    Eq.trans (cauchyCompletionContinuation_decode_encode_bhist h).symm
      (Eq.trans hread (cauchyCompletionContinuation_decode_encode_bhist k))

private theorem cauchyCompletionContinuation_mk_congr
    {Q1 Q2 B1 B2 S1 S2 W1 W2 D1 D2 R1 R2 E1 E2 H1 H2 C1 C2 P1 P2
      N1 N2 : BHist}
    (hQ : Q1 = Q2) (hB : B1 = B2) (hS : S1 = S2) (hW : W1 = W2)
    (hD : D1 = D2) (hR : R1 = R2) (hE : E1 = E2) (hH : H1 = H2)
    (hC : C1 = C2) (hP : P1 = P2) (hN : N1 = N2) :
    CauchyCompletionContinuationUp.mk Q1 B1 S1 W1 D1 R1 E1 H1 C1 P1 N1 =
      CauchyCompletionContinuationUp.mk Q2 B2 S2 W2 D2 R2 E2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hB
  cases hS
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyCompletionContinuationFields : CauchyCompletionContinuationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionContinuationUp.mk Q B S W D R E H C P N =>
      [Q, B, S, W, D, R, E, H, C, P, N]

def cauchyCompletionContinuationToEventFlow : CauchyCompletionContinuationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyCompletionContinuationEncodeBHist
      (cauchyCompletionContinuationFields x)

def cauchyCompletionContinuationFromEventFlow :
    EventFlow -> Option CauchyCompletionContinuationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
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
                                                    (CauchyCompletionContinuationUp.mk
                                                      (cauchyCompletionContinuationDecodeBHist Q)
                                                      (cauchyCompletionContinuationDecodeBHist B)
                                                      (cauchyCompletionContinuationDecodeBHist S)
                                                      (cauchyCompletionContinuationDecodeBHist W)
                                                      (cauchyCompletionContinuationDecodeBHist D)
                                                      (cauchyCompletionContinuationDecodeBHist R)
                                                      (cauchyCompletionContinuationDecodeBHist E)
                                                      (cauchyCompletionContinuationDecodeBHist H)
                                                      (cauchyCompletionContinuationDecodeBHist C)
                                                      (cauchyCompletionContinuationDecodeBHist P)
                                                      (cauchyCompletionContinuationDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyCompletionContinuation_round_trip :
    forall x : CauchyCompletionContinuationUp,
      cauchyCompletionContinuationFromEventFlow
        (cauchyCompletionContinuationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q B S W D R E H C P N =>
      change
        some
          (CauchyCompletionContinuationUp.mk
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist Q))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist B))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist S))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist W))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist D))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist R))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist E))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist H))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist C))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist P))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist N))) =
          some (CauchyCompletionContinuationUp.mk Q B S W D R E H C P N)
      exact
        congrArg some
          (cauchyCompletionContinuation_mk_congr
            (cauchyCompletionContinuation_decode_encode_bhist Q)
            (cauchyCompletionContinuation_decode_encode_bhist B)
            (cauchyCompletionContinuation_decode_encode_bhist S)
            (cauchyCompletionContinuation_decode_encode_bhist W)
            (cauchyCompletionContinuation_decode_encode_bhist D)
            (cauchyCompletionContinuation_decode_encode_bhist R)
            (cauchyCompletionContinuation_decode_encode_bhist E)
            (cauchyCompletionContinuation_decode_encode_bhist H)
            (cauchyCompletionContinuation_decode_encode_bhist C)
            (cauchyCompletionContinuation_decode_encode_bhist P)
            (cauchyCompletionContinuation_decode_encode_bhist N))

private theorem cauchyCompletionContinuationToEventFlow_injective
    {x y : CauchyCompletionContinuationUp} :
    cauchyCompletionContinuationToEventFlow x =
        cauchyCompletionContinuationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow x) =
        cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow y) :=
    congrArg cauchyCompletionContinuationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionContinuation_round_trip x).symm
      (Eq.trans hread (cauchyCompletionContinuation_round_trip y)))

instance cauchyCompletionContinuationBHistCarrier :
    BHistCarrier CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionContinuationToEventFlow
  fromEventFlow := cauchyCompletionContinuationFromEventFlow

instance cauchyCompletionContinuationChapterTasteGate :
    ChapterTasteGate CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionContinuationFromEventFlow
        (cauchyCompletionContinuationToEventFlow x) = some x
    exact cauchyCompletionContinuation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionContinuationToEventFlow_injective heq)

instance cauchyCompletionContinuationNontrivial :
    Nontrivial CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionContinuationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionContinuationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionContinuationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionContinuationChapterTasteGate

theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletionContinuationDecodeBHist
        (cauchyCompletionContinuationEncodeBHist h) = h) ∧
      (forall x : CauchyCompletionContinuationUp,
        cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow x) = some x) ∧
        (forall x y : CauchyCompletionContinuationUp,
          cauchyCompletionContinuationToEventFlow x =
              cauchyCompletionContinuationToEventFlow y ->
            x = y) ∧
          cauchyCompletionContinuationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyCompletionContinuation_decode_encode_bhist,
      cauchyCompletionContinuation_round_trip,
      (fun _ _ heq => cauchyCompletionContinuationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionContinuationUp.TasteGate

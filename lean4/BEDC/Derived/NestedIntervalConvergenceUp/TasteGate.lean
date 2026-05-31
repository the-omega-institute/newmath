import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalConvergenceUp : Type where
  | mk (N L W D E R Q H C P M : BHist) : NestedIntervalConvergenceUp

def nestedIntervalConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalConvergenceEncodeBHist h

def nestedIntervalConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalConvergenceDecodeBHist tail)

private theorem nestedIntervalConvergence_decode_encode_bhist :
    ∀ h : BHist,
      nestedIntervalConvergenceDecodeBHist (nestedIntervalConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem nestedIntervalConvergence_mk_congr
    {N N' L L' W W' D D' E E' R R' Q Q' H H' C C' P P' M M' : BHist}
    (hN : N' = N) (hL : L' = L) (hW : W' = W) (hD : D' = D)
    (hE : E' = E) (hR : R' = R) (hQ : Q' = Q) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hM : M' = M) :
    NestedIntervalConvergenceUp.mk N' L' W' D' E' R' Q' H' C' P' M' =
      NestedIntervalConvergenceUp.mk N L W D E R Q H C P M := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hN
  cases hL
  cases hW
  cases hD
  cases hE
  cases hR
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hM
  rfl

def nestedIntervalConvergenceFields : NestedIntervalConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalConvergenceUp.mk N L W D E R Q H C P M =>
      [N, L, W, D, E, R, Q, H, C, P, M]

def nestedIntervalConvergenceToEventFlow : NestedIntervalConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedIntervalConvergenceFields x).map nestedIntervalConvergenceEncodeBHist

def nestedIntervalConvergenceFromEventFlow : EventFlow → Option NestedIntervalConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | N :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
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
                                          | M :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (NestedIntervalConvergenceUp.mk
                                                      (nestedIntervalConvergenceDecodeBHist N)
                                                      (nestedIntervalConvergenceDecodeBHist L)
                                                      (nestedIntervalConvergenceDecodeBHist W)
                                                      (nestedIntervalConvergenceDecodeBHist D)
                                                      (nestedIntervalConvergenceDecodeBHist E)
                                                      (nestedIntervalConvergenceDecodeBHist R)
                                                      (nestedIntervalConvergenceDecodeBHist Q)
                                                      (nestedIntervalConvergenceDecodeBHist H)
                                                      (nestedIntervalConvergenceDecodeBHist C)
                                                      (nestedIntervalConvergenceDecodeBHist P)
                                                      (nestedIntervalConvergenceDecodeBHist M))
                                              | _ :: _ => none

private theorem nestedIntervalConvergence_round_trip :
    ∀ x : NestedIntervalConvergenceUp,
      nestedIntervalConvergenceFromEventFlow (nestedIntervalConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N L W D E R Q H C P M =>
      exact
        congrArg some
          (nestedIntervalConvergence_mk_congr
            (nestedIntervalConvergence_decode_encode_bhist N)
            (nestedIntervalConvergence_decode_encode_bhist L)
            (nestedIntervalConvergence_decode_encode_bhist W)
            (nestedIntervalConvergence_decode_encode_bhist D)
            (nestedIntervalConvergence_decode_encode_bhist E)
            (nestedIntervalConvergence_decode_encode_bhist R)
            (nestedIntervalConvergence_decode_encode_bhist Q)
            (nestedIntervalConvergence_decode_encode_bhist H)
            (nestedIntervalConvergence_decode_encode_bhist C)
            (nestedIntervalConvergence_decode_encode_bhist P)
            (nestedIntervalConvergence_decode_encode_bhist M))

private theorem nestedIntervalConvergenceToEventFlow_injective
    {x y : NestedIntervalConvergenceUp} :
    nestedIntervalConvergenceToEventFlow x = nestedIntervalConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalConvergenceFromEventFlow (nestedIntervalConvergenceToEventFlow x) =
        nestedIntervalConvergenceFromEventFlow (nestedIntervalConvergenceToEventFlow y) :=
    congrArg nestedIntervalConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedIntervalConvergence_round_trip x).symm
      (Eq.trans hread (nestedIntervalConvergence_round_trip y)))

instance nestedIntervalConvergenceBHistCarrier :
    BHistCarrier NestedIntervalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalConvergenceToEventFlow
  fromEventFlow := nestedIntervalConvergenceFromEventFlow

instance nestedIntervalConvergenceChapterTasteGate :
    ChapterTasteGate NestedIntervalConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalConvergenceFromEventFlow (nestedIntervalConvergenceToEventFlow x) =
      some x
    exact nestedIntervalConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalConvergenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NestedIntervalConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalConvergenceChapterTasteGate

theorem NestedIntervalConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedIntervalConvergenceDecodeBHist
      (nestedIntervalConvergenceEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalConvergenceUp,
        nestedIntervalConvergenceFromEventFlow
          (nestedIntervalConvergenceToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalConvergenceUp,
          nestedIntervalConvergenceToEventFlow x =
            nestedIntervalConvergenceToEventFlow y → x = y) ∧
          nestedIntervalConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nestedIntervalConvergence_decode_encode_bhist
  · constructor
    · exact nestedIntervalConvergence_round_trip
    · constructor
      · intro x y heq
        exact nestedIntervalConvergenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.NestedIntervalConvergenceUp

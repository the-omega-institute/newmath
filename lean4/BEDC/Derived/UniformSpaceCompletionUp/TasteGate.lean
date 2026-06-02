import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformSpaceCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformSpaceCompletionUp : Type where
  | mk (U F D S E H C P N : BHist) : UniformSpaceCompletionUp
  deriving DecidableEq

def uniformSpaceCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformSpaceCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformSpaceCompletionEncodeBHist h

def uniformSpaceCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformSpaceCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformSpaceCompletionDecodeBHist tail)

private theorem uniformSpaceCompletion_decode_encode_bhist :
    forall h : BHist,
      uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem UniformSpaceCompletionTasteGate_single_carrier_alignment_mk_congr
    {U1 U2 F1 F2 D1 D2 S1 S2 E1 E2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hU : U1 = U2) (hF : F1 = F2) (hD : D1 = D2) (hS : S1 = S2)
    (hE : E1 = E2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hN : N1 = N2) :
    UniformSpaceCompletionUp.mk U1 F1 D1 S1 E1 H1 C1 P1 N1 =
      UniformSpaceCompletionUp.mk U2 F2 D2 S2 E2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU
  cases hF
  cases hD
  cases hS
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def uniformSpaceCompletionFields : UniformSpaceCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformSpaceCompletionUp.mk U F D S E H C P N => [U, F, D, S, E, H, C, P, N]

def uniformSpaceCompletionToEventFlow : UniformSpaceCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map uniformSpaceCompletionEncodeBHist (uniformSpaceCompletionFields x)

def uniformSpaceCompletionFromEventFlow : EventFlow -> Option UniformSpaceCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | U :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (UniformSpaceCompletionUp.mk
                                              (uniformSpaceCompletionDecodeBHist U)
                                              (uniformSpaceCompletionDecodeBHist F)
                                              (uniformSpaceCompletionDecodeBHist D)
                                              (uniformSpaceCompletionDecodeBHist S)
                                              (uniformSpaceCompletionDecodeBHist E)
                                              (uniformSpaceCompletionDecodeBHist H)
                                              (uniformSpaceCompletionDecodeBHist C)
                                              (uniformSpaceCompletionDecodeBHist P)
                                              (uniformSpaceCompletionDecodeBHist N))
                                      | _ :: _ => none

private theorem uniformSpaceCompletion_round_trip :
    forall x : UniformSpaceCompletionUp,
      uniformSpaceCompletionFromEventFlow (uniformSpaceCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U F D S E H C P N =>
      change
        some
          (UniformSpaceCompletionUp.mk
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist U))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist F))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist D))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist S))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist E))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist H))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist C))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist P))
            (uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist N))) =
          some (UniformSpaceCompletionUp.mk U F D S E H C P N)
      exact
        congrArg some
          (UniformSpaceCompletionTasteGate_single_carrier_alignment_mk_congr
            (uniformSpaceCompletion_decode_encode_bhist U)
            (uniformSpaceCompletion_decode_encode_bhist F)
            (uniformSpaceCompletion_decode_encode_bhist D)
            (uniformSpaceCompletion_decode_encode_bhist S)
            (uniformSpaceCompletion_decode_encode_bhist E)
            (uniformSpaceCompletion_decode_encode_bhist H)
            (uniformSpaceCompletion_decode_encode_bhist C)
            (uniformSpaceCompletion_decode_encode_bhist P)
            (uniformSpaceCompletion_decode_encode_bhist N))

private theorem UniformSpaceCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformSpaceCompletionUp} :
    uniformSpaceCompletionToEventFlow x = uniformSpaceCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformSpaceCompletionFromEventFlow (uniformSpaceCompletionToEventFlow x) =
        uniformSpaceCompletionFromEventFlow (uniformSpaceCompletionToEventFlow y) :=
    congrArg uniformSpaceCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformSpaceCompletion_round_trip x).symm
      (Eq.trans hread (uniformSpaceCompletion_round_trip y)))

instance uniformSpaceCompletionBHistCarrier : BHistCarrier UniformSpaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformSpaceCompletionToEventFlow
  fromEventFlow := uniformSpaceCompletionFromEventFlow

instance uniformSpaceCompletionChapterTasteGate : ChapterTasteGate UniformSpaceCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformSpaceCompletionFromEventFlow (uniformSpaceCompletionToEventFlow x) = some x
    exact uniformSpaceCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformSpaceCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformSpaceCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformSpaceCompletionDecodeBHist (uniformSpaceCompletionEncodeBHist h) = h) ∧
      (forall x : UniformSpaceCompletionUp,
        uniformSpaceCompletionFromEventFlow (uniformSpaceCompletionToEventFlow x) = some x) ∧
        (forall x y : UniformSpaceCompletionUp,
          uniformSpaceCompletionToEventFlow x = uniformSpaceCompletionToEventFlow y -> x = y) ∧
          uniformSpaceCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact uniformSpaceCompletion_decode_encode_bhist
  · constructor
    · exact uniformSpaceCompletion_round_trip
    · constructor
      · exact fun _x _y heq =>
          UniformSpaceCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformSpaceCompletionUp

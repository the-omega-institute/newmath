import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NonAxiomAdmissionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NonAxiomAdmissionUp : Type where
  | mk : (X F W H C P N : BHist) → NonAxiomAdmissionUp
  deriving DecidableEq

private def nonAxiomAdmissionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nonAxiomAdmissionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nonAxiomAdmissionEncodeBHist h

private def nonAxiomAdmissionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nonAxiomAdmissionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nonAxiomAdmissionDecodeBHist tail)

private theorem nonAxiomAdmissionDecode_encode_bhist :
    ∀ h : BHist, nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def nonAxiomAdmissionToEventFlow : NonAxiomAdmissionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NonAxiomAdmissionUp.mk X F W H C P N =>
      [[BMark.b0],
        nonAxiomAdmissionEncodeBHist X,
        [BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomAdmissionEncodeBHist N]

private def nonAxiomAdmissionFromEventFlow : EventFlow → Option NonAxiomAdmissionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | X :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (NonAxiomAdmissionUp.mk
                                                                  (nonAxiomAdmissionDecodeBHist X)
                                                                  (nonAxiomAdmissionDecodeBHist F)
                                                                  (nonAxiomAdmissionDecodeBHist W)
                                                                  (nonAxiomAdmissionDecodeBHist H)
                                                                  (nonAxiomAdmissionDecodeBHist C)
                                                                  (nonAxiomAdmissionDecodeBHist P)
                                                                  (nonAxiomAdmissionDecodeBHist N))
                                                          | _ :: _ => none

private theorem nonAxiomAdmission_round_trip :
    ∀ x : NonAxiomAdmissionUp,
      nonAxiomAdmissionFromEventFlow (nonAxiomAdmissionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F W H C P N =>
      change
        some
          (NonAxiomAdmissionUp.mk
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist X))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist F))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist W))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist H))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist C))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist P))
            (nonAxiomAdmissionDecodeBHist (nonAxiomAdmissionEncodeBHist N))) =
          some (NonAxiomAdmissionUp.mk X F W H C P N)
      rw [nonAxiomAdmissionDecode_encode_bhist X, nonAxiomAdmissionDecode_encode_bhist F,
        nonAxiomAdmissionDecode_encode_bhist W, nonAxiomAdmissionDecode_encode_bhist H,
        nonAxiomAdmissionDecode_encode_bhist C, nonAxiomAdmissionDecode_encode_bhist P,
        nonAxiomAdmissionDecode_encode_bhist N]

private theorem nonAxiomAdmissionToEventFlow_injective {x y : NonAxiomAdmissionUp} :
    nonAxiomAdmissionToEventFlow x = nonAxiomAdmissionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nonAxiomAdmissionFromEventFlow (nonAxiomAdmissionToEventFlow x) =
        nonAxiomAdmissionFromEventFlow (nonAxiomAdmissionToEventFlow y) :=
    congrArg nonAxiomAdmissionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nonAxiomAdmission_round_trip x).symm
      (Eq.trans hread (nonAxiomAdmission_round_trip y)))

instance nonAxiomAdmissionBHistCarrier : BHistCarrier NonAxiomAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nonAxiomAdmissionToEventFlow
  fromEventFlow := nonAxiomAdmissionFromEventFlow

instance nonAxiomAdmissionChapterTasteGate : ChapterTasteGate NonAxiomAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nonAxiomAdmissionFromEventFlow (nonAxiomAdmissionToEventFlow x) = some x
    exact nonAxiomAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nonAxiomAdmissionToEventFlow_injective heq)

instance nonAxiomAdmissionFieldFaithful : FieldFaithful NonAxiomAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | NonAxiomAdmissionUp.mk X F W H C P N => [X, F, W, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk X1 F1 W1 H1 C1 P1 N1 =>
        cases y with
        | mk X2 F2 W2 H2 C2 P2 N2 =>
            injection h with hX t1
            injection t1 with hF t2
            injection t2 with hW t3
            injection t3 with hH t4
            injection t4 with hC t5
            injection t5 with hP t6
            injection t6 with hN _
            cases hX
            cases hF
            cases hW
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance nonAxiomAdmissionNontrivial : Nontrivial NonAxiomAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NonAxiomAdmissionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      NonAxiomAdmissionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NonAxiomAdmissionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nonAxiomAdmissionChapterTasteGate

end BEDC.Derived.NonAxiomAdmissionUp

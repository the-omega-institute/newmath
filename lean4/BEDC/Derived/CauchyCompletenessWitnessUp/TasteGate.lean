import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletenessWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletenessWitnessUp : Type where
  | mk (R S D M E H C P N : BHist) : CauchyCompletenessWitnessUp
  deriving DecidableEq

def cauchyCompletenessWitnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletenessWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletenessWitnessEncodeBHist h

def cauchyCompletenessWitnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletenessWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletenessWitnessDecodeBHist tail)

theorem CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cauchyCompletenessWitness_mk_congr
    {R R' S S' D D' M M' E E' H H' C C' P P' N N' : BHist}
    (hR : R' = R)
    (hS : S' = S)
    (hD : D' = D)
    (hM : M' = M)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CauchyCompletenessWitnessUp.mk R' S' D' M' E' H' C' P' N' =
      CauchyCompletenessWitnessUp.mk R S D M E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hS
  cases hD
  cases hM
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyCompletenessWitnessFields : CauchyCompletenessWitnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletenessWitnessUp.mk R S D M E H C P N => [R, S, D, M, E, H, C, P, N]

def cauchyCompletenessWitnessToEventFlow : CauchyCompletenessWitnessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletenessWitnessFields x).map cauchyCompletenessWitnessEncodeBHist

def cauchyCompletenessWitnessFromEventFlow : EventFlow -> Option CauchyCompletenessWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
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
                                            (CauchyCompletenessWitnessUp.mk
                                              (cauchyCompletenessWitnessDecodeBHist R)
                                              (cauchyCompletenessWitnessDecodeBHist S)
                                              (cauchyCompletenessWitnessDecodeBHist D)
                                              (cauchyCompletenessWitnessDecodeBHist M)
                                              (cauchyCompletenessWitnessDecodeBHist E)
                                              (cauchyCompletenessWitnessDecodeBHist H)
                                              (cauchyCompletenessWitnessDecodeBHist C)
                                              (cauchyCompletenessWitnessDecodeBHist P)
                                              (cauchyCompletenessWitnessDecodeBHist N))
                                      | _ :: _ => none

private theorem cauchyCompletenessWitness_round_trip :
    ∀ x : CauchyCompletenessWitnessUp,
      cauchyCompletenessWitnessFromEventFlow (cauchyCompletenessWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D M E H C P N =>
      change
        some
          (CauchyCompletenessWitnessUp.mk
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist R))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist S))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist D))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist M))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist E))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist H))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist C))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist P))
            (cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist N))) =
          some (CauchyCompletenessWitnessUp.mk R S D M E H C P N)
      exact
        congrArg some
          (cauchyCompletenessWitness_mk_congr
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode R)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode S)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode D)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode M)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode E)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode H)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode C)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode P)
            (CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode N))

private theorem cauchyCompletenessWitnessToEventFlow_injective
    {x y : CauchyCompletenessWitnessUp} :
    cauchyCompletenessWitnessToEventFlow x = cauchyCompletenessWitnessToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletenessWitnessFromEventFlow (cauchyCompletenessWitnessToEventFlow x) =
        cauchyCompletenessWitnessFromEventFlow (cauchyCompletenessWitnessToEventFlow y) :=
    congrArg cauchyCompletenessWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletenessWitness_round_trip x).symm
      (Eq.trans hread (cauchyCompletenessWitness_round_trip y)))

private theorem cauchyCompletenessWitness_fields_faithful :
    ∀ x y : CauchyCompletenessWitnessUp,
      cauchyCompletenessWitnessFields x = cauchyCompletenessWitnessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 S1 D1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 S2 D2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletenessWitnessBHistCarrier :
    BHistCarrier CauchyCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletenessWitnessToEventFlow
  fromEventFlow := cauchyCompletenessWitnessFromEventFlow

instance cauchyCompletenessWitnessChapterTasteGate :
    ChapterTasteGate CauchyCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletenessWitnessFromEventFlow (cauchyCompletenessWitnessToEventFlow x) =
        some x
    exact cauchyCompletenessWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletenessWitnessToEventFlow_injective heq)

instance cauchyCompletenessWitnessFieldFaithful :
    FieldFaithful CauchyCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletenessWitnessFields
  field_faithful := cauchyCompletenessWitness_fields_faithful

instance cauchyCompletenessWitnessNontrivial : Nontrivial CauchyCompletenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletenessWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletenessWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletenessWitnessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletenessWitnessDecodeBHist (cauchyCompletenessWitnessEncodeBHist h) = h) ∧
      (forall x : CauchyCompletenessWitnessUp,
        cauchyCompletenessWitnessFromEventFlow (cauchyCompletenessWitnessToEventFlow x) =
          some x) ∧
        (forall x y : CauchyCompletenessWitnessUp,
          cauchyCompletenessWitnessToEventFlow x =
            cauchyCompletenessWitnessToEventFlow y -> x = y) ∧
          cauchyCompletenessWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCompletenessWitnessTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact cauchyCompletenessWitness_round_trip
    · constructor
      · intro x y heq
        exact cauchyCompletenessWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyCompletenessWitnessUp

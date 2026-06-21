import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailEquivalenceUp : Type where
  | mk (S0 S1 R0 R1 D Q A H C P N : BHist) : RegularCauchyTailEquivalenceUp
  deriving DecidableEq

def regularCauchyTailEquivalenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailEquivalenceEncodeBHist h

def regularCauchyTailEquivalenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailEquivalenceDecodeBHist tail)

theorem RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyTailEquivalenceDecodeBHist
        (regularCauchyTailEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_some_mk
    {S0 S1 R0 R1 D Q A H C P N S0' S1' R0' R1' D' Q' A' H' C' P' N' : BHist}
    (hS0 : S0' = S0) (hS1 : S1' = S1) (hR0 : R0' = R0) (hR1 : R1' = R1)
    (hD : D' = D) (hQ : Q' = Q) (hA : A' = A) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    some (RegularCauchyTailEquivalenceUp.mk S0' S1' R0' R1' D' Q' A' H' C' P' N') =
      some (RegularCauchyTailEquivalenceUp.mk S0 S1 R0 R1 D Q A H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS0
  cases hS1
  cases hR0
  cases hR1
  cases hD
  cases hQ
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyTailEquivalenceFields :
    RegularCauchyTailEquivalenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailEquivalenceUp.mk S0 S1 R0 R1 D Q A H C P N =>
      [S0, S1, R0, R1, D, Q, A, H, C, P, N]

def regularCauchyTailEquivalenceToEventFlow :
    RegularCauchyTailEquivalenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailEquivalenceFields x).map regularCauchyTailEquivalenceEncodeBHist

def regularCauchyTailEquivalenceFromEventFlow :
    EventFlow -> Option RegularCauchyTailEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S0 :: rest0 =>
      match rest0 with
      | [] => none
      | S1 :: rest1 =>
          match rest1 with
          | [] => none
          | R0 :: rest2 =>
              match rest2 with
              | [] => none
              | R1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
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
                                                    (RegularCauchyTailEquivalenceUp.mk
                                                      (regularCauchyTailEquivalenceDecodeBHist S0)
                                                      (regularCauchyTailEquivalenceDecodeBHist S1)
                                                      (regularCauchyTailEquivalenceDecodeBHist R0)
                                                      (regularCauchyTailEquivalenceDecodeBHist R1)
                                                      (regularCauchyTailEquivalenceDecodeBHist D)
                                                      (regularCauchyTailEquivalenceDecodeBHist Q)
                                                      (regularCauchyTailEquivalenceDecodeBHist A)
                                                      (regularCauchyTailEquivalenceDecodeBHist H)
                                                      (regularCauchyTailEquivalenceDecodeBHist C)
                                                      (regularCauchyTailEquivalenceDecodeBHist P)
                                                      (regularCauchyTailEquivalenceDecodeBHist N))
                                              | _ :: _ => none

theorem RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyTailEquivalenceUp,
      regularCauchyTailEquivalenceFromEventFlow
        (regularCauchyTailEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 R0 R1 D Q A H C P N =>
      exact
        RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_some_mk
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode S0)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode S1)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode R0)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode R1)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode D)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode Q)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode A)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode H)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode C)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode P)
          (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode N)

theorem RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailEquivalenceUp} :
    regularCauchyTailEquivalenceToEventFlow x =
      regularCauchyTailEquivalenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailEquivalenceFromEventFlow
          (regularCauchyTailEquivalenceToEventFlow x) =
        regularCauchyTailEquivalenceFromEventFlow
          (regularCauchyTailEquivalenceToEventFlow y) :=
    congrArg regularCauchyTailEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyTailEquivalenceBHistCarrier :
    BHistCarrier RegularCauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailEquivalenceToEventFlow
  fromEventFlow := regularCauchyTailEquivalenceFromEventFlow

instance regularCauchyTailEquivalenceChapterTasteGate :
    ChapterTasteGate RegularCauchyTailEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailEquivalenceFromEventFlow
        (regularCauchyTailEquivalenceToEventFlow x) = some x
    exact RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyTailEquivalenceDecodeBHist
        (regularCauchyTailEquivalenceEncodeBHist h) = h) /\
      (forall x : RegularCauchyTailEquivalenceUp,
        regularCauchyTailEquivalenceFromEventFlow
          (regularCauchyTailEquivalenceToEventFlow x) = some x) /\
        (forall x y : RegularCauchyTailEquivalenceUp,
          regularCauchyTailEquivalenceToEventFlow x =
            regularCauchyTailEquivalenceToEventFlow y -> x = y) /\
          regularCauchyTailEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          RegularCauchyTailEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.RegularCauchyTailEquivalenceUp

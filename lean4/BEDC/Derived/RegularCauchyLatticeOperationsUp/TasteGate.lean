import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLatticeOperationsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLatticeOperationsUp : Type where
  | mk (X Y T D M A R E H C P N : BHist) : RegularCauchyLatticeOperationsUp
  deriving DecidableEq

def regularCauchyLatticeOperationsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLatticeOperationsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLatticeOperationsEncodeBHist h

def regularCauchyLatticeOperationsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLatticeOperationsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLatticeOperationsDecodeBHist tail)

private theorem regularCauchyLatticeOperations_decode_encode :
    forall h : BHist,
      regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLatticeOperationsFields :
    RegularCauchyLatticeOperationsUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLatticeOperationsUp.mk X Y T D M A R E H C P N =>
      [X, Y, T, D, M, A, R, E, H, C, P, N]

def regularCauchyLatticeOperationsToEventFlow :
    RegularCauchyLatticeOperationsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyLatticeOperationsFields x).map
        regularCauchyLatticeOperationsEncodeBHist

def regularCauchyLatticeOperationsFromEventFlow :
    EventFlow -> Option RegularCauchyLatticeOperationsUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | Y :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
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
                                                        (RegularCauchyLatticeOperationsUp.mk
                                                          (regularCauchyLatticeOperationsDecodeBHist X)
                                                          (regularCauchyLatticeOperationsDecodeBHist Y)
                                                          (regularCauchyLatticeOperationsDecodeBHist T)
                                                          (regularCauchyLatticeOperationsDecodeBHist D)
                                                          (regularCauchyLatticeOperationsDecodeBHist M)
                                                          (regularCauchyLatticeOperationsDecodeBHist A)
                                                          (regularCauchyLatticeOperationsDecodeBHist R)
                                                          (regularCauchyLatticeOperationsDecodeBHist E)
                                                          (regularCauchyLatticeOperationsDecodeBHist H)
                                                          (regularCauchyLatticeOperationsDecodeBHist C)
                                                          (regularCauchyLatticeOperationsDecodeBHist P)
                                                          (regularCauchyLatticeOperationsDecodeBHist N))
                                                  | _ :: _ => none

private theorem regularCauchyLatticeOperations_round_trip :
    forall x : RegularCauchyLatticeOperationsUp,
      regularCauchyLatticeOperationsFromEventFlow
        (regularCauchyLatticeOperationsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T D M A R E H C P N =>
      change
        some
          (RegularCauchyLatticeOperationsUp.mk
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist X))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist Y))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist T))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist D))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist M))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist A))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist R))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist E))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist H))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist C))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist P))
            (regularCauchyLatticeOperationsDecodeBHist
              (regularCauchyLatticeOperationsEncodeBHist N))) =
          some (RegularCauchyLatticeOperationsUp.mk X Y T D M A R E H C P N)
      rw [regularCauchyLatticeOperations_decode_encode X,
        regularCauchyLatticeOperations_decode_encode Y,
        regularCauchyLatticeOperations_decode_encode T,
        regularCauchyLatticeOperations_decode_encode D,
        regularCauchyLatticeOperations_decode_encode M,
        regularCauchyLatticeOperations_decode_encode A,
        regularCauchyLatticeOperations_decode_encode R,
        regularCauchyLatticeOperations_decode_encode E,
        regularCauchyLatticeOperations_decode_encode H,
        regularCauchyLatticeOperations_decode_encode C,
        regularCauchyLatticeOperations_decode_encode P,
        regularCauchyLatticeOperations_decode_encode N]

private theorem regularCauchyLatticeOperationsToEventFlow_injective
    {x y : RegularCauchyLatticeOperationsUp} :
    regularCauchyLatticeOperationsToEventFlow x =
        regularCauchyLatticeOperationsToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) =
        regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow y) :=
    congrArg regularCauchyLatticeOperationsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLatticeOperations_round_trip x).symm
      (Eq.trans hread (regularCauchyLatticeOperations_round_trip y)))

private theorem regularCauchyLatticeOperations_field_faithful :
    forall x y : RegularCauchyLatticeOperationsUp,
      regularCauchyLatticeOperationsFields x =
          regularCauchyLatticeOperationsFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 T1 D1 M1 A1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 T2 D2 M2 A2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyLatticeOperationsBHistCarrier :
    BHistCarrier RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLatticeOperationsToEventFlow
  fromEventFlow := regularCauchyLatticeOperationsFromEventFlow

instance regularCauchyLatticeOperationsChapterTasteGate :
    ChapterTasteGate RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) =
        some x
    exact regularCauchyLatticeOperations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLatticeOperationsToEventFlow_injective heq)

instance regularCauchyLatticeOperationsFieldFaithful :
    FieldFaithful RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLatticeOperationsFields
  field_faithful := regularCauchyLatticeOperations_field_faithful

instance regularCauchyLatticeOperationsNontrivial :
    Nontrivial RegularCauchyLatticeOperationsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLatticeOperationsUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyLatticeOperationsUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyLatticeOperationsTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyLatticeOperationsDecodeBHist
        (regularCauchyLatticeOperationsEncodeBHist h) = h) ∧
      (forall x : RegularCauchyLatticeOperationsUp,
        regularCauchyLatticeOperationsFromEventFlow
          (regularCauchyLatticeOperationsToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyLatticeOperationsUp,
          regularCauchyLatticeOperationsToEventFlow x =
              regularCauchyLatticeOperationsToEventFlow y ->
            x = y) ∧
          regularCauchyLatticeOperationsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact regularCauchyLatticeOperations_decode_encode
  · constructor
    · exact regularCauchyLatticeOperations_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyLatticeOperationsToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyLatticeOperationsUp

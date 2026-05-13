import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalConsistencyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalConsistencyBoundaryUp : Type where
  | mk :
      (typing closed normal falseRow obstruction refusal transport route provenance nameCert :
        BHist) ->
      ClosedNormalConsistencyBoundaryUp
  deriving DecidableEq

def closedNormalConsistencyBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalConsistencyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalConsistencyBoundaryEncodeBHist h

def closedNormalConsistencyBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalConsistencyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalConsistencyBoundaryDecodeBHist tail)

private theorem ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      closedNormalConsistencyBoundaryDecodeBHist
        (closedNormalConsistencyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedNormalConsistencyBoundaryToEventFlow :
    ClosedNormalConsistencyBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConsistencyBoundaryUp.mk typing closed normal falseRow obstruction refusal
      transport route provenance nameCert =>
      [[BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist typing,
        [BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist closed,
        [BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist falseRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closedNormalConsistencyBoundaryEncodeBHist nameCert]

def closedNormalConsistencyBoundaryFromEventFlow :
    EventFlow -> Option ClosedNormalConsistencyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typing :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | normal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | falseRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ClosedNormalConsistencyBoundaryUp.mk
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist typing)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist closed)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist normal)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist falseRow)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist obstruction)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist refusal)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist transport)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist route)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist provenance)
                                                                                          (closedNormalConsistencyBoundaryDecodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip :
    forall x : ClosedNormalConsistencyBoundaryUp,
      closedNormalConsistencyBoundaryFromEventFlow
        (closedNormalConsistencyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typing closed normal falseRow obstruction refusal transport route provenance nameCert =>
      change
        some
          (ClosedNormalConsistencyBoundaryUp.mk
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist typing))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist closed))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist normal))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist falseRow))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist obstruction))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist refusal))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist transport))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist route))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist provenance))
            (closedNormalConsistencyBoundaryDecodeBHist
              (closedNormalConsistencyBoundaryEncodeBHist nameCert))) =
          some
            (ClosedNormalConsistencyBoundaryUp.mk typing closed normal falseRow obstruction
              refusal transport route provenance nameCert)
      rw [ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode typing,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode closed,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode normal,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode falseRow,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode obstruction,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode refusal,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode transport,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode route,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode provenance,
        ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode nameCert]

private theorem ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_injective
    {x y : ClosedNormalConsistencyBoundaryUp} :
    closedNormalConsistencyBoundaryToEventFlow x =
      closedNormalConsistencyBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow x) =
        closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow y) :=
    congrArg closedNormalConsistencyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance closedNormalConsistencyBoundaryBHistCarrier :
    BHistCarrier ClosedNormalConsistencyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConsistencyBoundaryToEventFlow
  fromEventFlow := closedNormalConsistencyBoundaryFromEventFlow

instance closedNormalConsistencyBoundaryChapterTasteGate :
    ChapterTasteGate ClosedNormalConsistencyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedNormalConsistencyBoundaryFromEventFlow
      (closedNormalConsistencyBoundaryToEventFlow x) = some x
    exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_injective heq)

theorem ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedNormalConsistencyBoundaryDecodeBHist
        (closedNormalConsistencyBoundaryEncodeBHist h) = h) ∧
      (forall x : ClosedNormalConsistencyBoundaryUp,
        closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow x) = some x) ∧
        (forall x : ClosedNormalConsistencyBoundaryUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (forall x y : ClosedNormalConsistencyBoundaryUp,
            closedNormalConsistencyBoundaryToEventFlow x =
              closedNormalConsistencyBoundaryToEventFlow y -> x = y) ∧
            (forall x y : ClosedNormalConsistencyBoundaryUp,
              BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y -> x = y) ∧
              (forall (x : ClosedNormalConsistencyBoundaryUp) w m,
                List.Mem w (BHistCarrier.toEventFlow x) ->
                List.Mem m w -> m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x
        change closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow x) = some x
        exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_round_trip x
      · constructor
        · intro x y heq
          exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_injective heq
        · constructor
          · intro x y heq
            change closedNormalConsistencyBoundaryToEventFlow x =
              closedNormalConsistencyBoundaryToEventFlow y at heq
            exact ClosedNormalConsistencyBoundaryTasteGate_single_carrier_alignment_injective heq
          · intro x w m hw hm
            exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

end BEDC.Derived.ClosedNormalConsistencyBoundaryUp

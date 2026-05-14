import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyWitnessGridUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyWitnessGridUp : Type where
  | mk :
      (selector ledger classifier tail stream regular real transport route provenance
        localName : BHist) → RealCauchyWitnessGridUp
  deriving DecidableEq

def realCauchyWitnessGridEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyWitnessGridEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyWitnessGridEncodeBHist h

def realCauchyWitnessGridDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyWitnessGridDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyWitnessGridDecodeBHist tail)

private theorem realCauchyWitnessGrid_decode_encode_bhist :
    ∀ h : BHist,
      realCauchyWitnessGridDecodeBHist
        (realCauchyWitnessGridEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCauchyWitnessGridToEventFlow : RealCauchyWitnessGridUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyWitnessGridUp.mk selector ledger classifier tail stream regular real
      transport route provenance localName =>
      [[BMark.b0],
        realCauchyWitnessGridEncodeBHist selector,
        [BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCauchyWitnessGridEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCauchyWitnessGridEncodeBHist localName]

def realCauchyWitnessGridFromEventFlow :
    EventFlow → Option RealCauchyWitnessGridUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selector :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ledger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tail :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stream :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | regular :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | real :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match
                                                                            rest17 with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | localName ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (RealCauchyWitnessGridUp.mk
                                                                                                  (realCauchyWitnessGridDecodeBHist selector)
                                                                                                  (realCauchyWitnessGridDecodeBHist ledger)
                                                                                                  (realCauchyWitnessGridDecodeBHist classifier)
                                                                                                  (realCauchyWitnessGridDecodeBHist tail)
                                                                                                  (realCauchyWitnessGridDecodeBHist stream)
                                                                                                  (realCauchyWitnessGridDecodeBHist regular)
                                                                                                  (realCauchyWitnessGridDecodeBHist real)
                                                                                                  (realCauchyWitnessGridDecodeBHist transport)
                                                                                                  (realCauchyWitnessGridDecodeBHist route)
                                                                                                  (realCauchyWitnessGridDecodeBHist provenance)
                                                                                                  (realCauchyWitnessGridDecodeBHist localName))
                                                                                          | _ ::
                                                                                              _ =>
                                                                                              none

private theorem realCauchyWitnessGrid_round_trip :
    ∀ x : RealCauchyWitnessGridUp,
      realCauchyWitnessGridFromEventFlow
        (realCauchyWitnessGridToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selector ledger classifier tail stream regular real transport route provenance
      localName =>
      change
        some
          (RealCauchyWitnessGridUp.mk
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist selector))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist ledger))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist classifier))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist tail))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist stream))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist regular))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist real))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist transport))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist route))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist provenance))
            (realCauchyWitnessGridDecodeBHist
              (realCauchyWitnessGridEncodeBHist localName))) =
          some
            (RealCauchyWitnessGridUp.mk selector ledger classifier tail stream regular
              real transport route provenance localName)
      rw [realCauchyWitnessGrid_decode_encode_bhist selector,
        realCauchyWitnessGrid_decode_encode_bhist ledger,
        realCauchyWitnessGrid_decode_encode_bhist classifier,
        realCauchyWitnessGrid_decode_encode_bhist tail,
        realCauchyWitnessGrid_decode_encode_bhist stream,
        realCauchyWitnessGrid_decode_encode_bhist regular,
        realCauchyWitnessGrid_decode_encode_bhist real,
        realCauchyWitnessGrid_decode_encode_bhist transport,
        realCauchyWitnessGrid_decode_encode_bhist route,
        realCauchyWitnessGrid_decode_encode_bhist provenance,
        realCauchyWitnessGrid_decode_encode_bhist localName]

private theorem realCauchyWitnessGridToEventFlow_injective
    {x y : RealCauchyWitnessGridUp} :
    realCauchyWitnessGridToEventFlow x =
      realCauchyWitnessGridToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyWitnessGridFromEventFlow
          (realCauchyWitnessGridToEventFlow x) =
        realCauchyWitnessGridFromEventFlow
          (realCauchyWitnessGridToEventFlow y) :=
    congrArg realCauchyWitnessGridFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyWitnessGrid_round_trip x).symm
      (Eq.trans hread (realCauchyWitnessGrid_round_trip y)))

def realCauchyWitnessGridFields : RealCauchyWitnessGridUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyWitnessGridUp.mk selector ledger classifier tail stream regular real transport
      route provenance localName =>
      [selector, ledger, classifier, tail, stream, regular, real, transport, route,
        provenance, localName]

private theorem RealCauchyWitnessGridTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealCauchyWitnessGridUp,
      realCauchyWitnessGridFields x = realCauchyWitnessGridFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk selector ledger classifier tail stream regular real transport route provenance
      localName =>
      cases y with
      | mk selector' ledger' classifier' tail' stream' regular' real' transport' route'
          provenance' localName' =>
          cases hfields
          rfl

instance realCauchyWitnessGridBHistCarrier :
    BHistCarrier RealCauchyWitnessGridUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyWitnessGridToEventFlow
  fromEventFlow := realCauchyWitnessGridFromEventFlow

instance realCauchyWitnessGridChapterTasteGate :
    ChapterTasteGate RealCauchyWitnessGridUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCauchyWitnessGridFromEventFlow
        (realCauchyWitnessGridToEventFlow x) = some x
    exact realCauchyWitnessGrid_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyWitnessGridToEventFlow_injective heq)

instance realCauchyWitnessGridFieldFaithful :
    FieldFaithful RealCauchyWitnessGridUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCauchyWitnessGridFields
  field_faithful := RealCauchyWitnessGridTasteGate_single_carrier_alignment_field_faithful

theorem RealCauchyWitnessGridTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCauchyWitnessGridDecodeBHist
      (realCauchyWitnessGridEncodeBHist h) = h) ∧
      (∀ x : RealCauchyWitnessGridUp,
        realCauchyWitnessGridFromEventFlow
          (realCauchyWitnessGridToEventFlow x) = some x) ∧
      (∀ x y : RealCauchyWitnessGridUp,
        realCauchyWitnessGridToEventFlow x =
          realCauchyWitnessGridToEventFlow y → x = y) ∧
      realCauchyWitnessGridEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact realCauchyWitnessGrid_decode_encode_bhist
  · constructor
    · exact realCauchyWitnessGrid_round_trip
    · constructor
      · intro x y heq
        exact realCauchyWitnessGridToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealCauchyWitnessGridUp

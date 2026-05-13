import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TheorySelfClassifierUp : Type where
  | mk :
      (generator equality recursor purity boundary ledger transport route provenance name :
        BHist) ->
      TheorySelfClassifierUp
  deriving DecidableEq

def theorySelfClassifierEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: theorySelfClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: theorySelfClassifierEncodeBHist h

def theorySelfClassifierDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (theorySelfClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (theorySelfClassifierDecodeBHist tail)

private theorem theorySelfClassifier_decode_encode_bhist :
    forall h : BHist,
      theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem theorySelfClassifier_mk_congr
    {generator generator' equality equality' recursor recursor' purity purity' boundary
      boundary' ledger ledger' transport transport' route route' provenance provenance'
      name name' : BHist}
    (hGenerator : generator' = generator)
    (hEquality : equality' = equality)
    (hRecursor : recursor' = recursor)
    (hPurity : purity' = purity)
    (hBoundary : boundary' = boundary)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    TheorySelfClassifierUp.mk generator' equality' recursor' purity' boundary' ledger'
        transport' route' provenance' name' =
      TheorySelfClassifierUp.mk generator equality recursor purity boundary ledger transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerator
  cases hEquality
  cases hRecursor
  cases hPurity
  cases hBoundary
  cases hLedger
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def theorySelfClassifierToEventFlow : TheorySelfClassifierUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TheorySelfClassifierUp.mk generator equality recursor purity boundary ledger transport route
      provenance name =>
      [[BMark.b0],
        theorySelfClassifierEncodeBHist generator,
        [BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist equality,
        [BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist recursor,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist purity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        theorySelfClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        theorySelfClassifierEncodeBHist name]

def theorySelfClassifierFromEventFlow : EventFlow -> Option TheorySelfClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | equality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recursor :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | purity :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
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
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (TheorySelfClassifierUp.mk
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            generator)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            equality)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            recursor)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            purity)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            boundary)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            ledger)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            transport)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            route)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            provenance)
                                                                                          (theorySelfClassifierDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

def theorySelfClassifierFields : TheorySelfClassifierUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TheorySelfClassifierUp.mk generator equality recursor purity boundary ledger transport route
      provenance name =>
      [generator, equality, recursor, purity, boundary, ledger, transport, route, provenance,
        name]

private theorem theorySelfClassifier_round_trip :
    forall x : TheorySelfClassifierUp,
      theorySelfClassifierFromEventFlow (theorySelfClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator equality recursor purity boundary ledger transport route provenance name =>
      change
        some
          (TheorySelfClassifierUp.mk
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist generator))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist equality))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist recursor))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist purity))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist boundary))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist ledger))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist transport))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist route))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist provenance))
            (theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist name))) =
          some
            (TheorySelfClassifierUp.mk generator equality recursor purity boundary ledger
              transport route provenance name)
      exact
        congrArg some
          (theorySelfClassifier_mk_congr
            (theorySelfClassifier_decode_encode_bhist generator)
            (theorySelfClassifier_decode_encode_bhist equality)
            (theorySelfClassifier_decode_encode_bhist recursor)
            (theorySelfClassifier_decode_encode_bhist purity)
            (theorySelfClassifier_decode_encode_bhist boundary)
            (theorySelfClassifier_decode_encode_bhist ledger)
            (theorySelfClassifier_decode_encode_bhist transport)
            (theorySelfClassifier_decode_encode_bhist route)
            (theorySelfClassifier_decode_encode_bhist provenance)
            (theorySelfClassifier_decode_encode_bhist name))

private theorem theorySelfClassifierToEventFlow_injective {x y : TheorySelfClassifierUp} :
    theorySelfClassifierToEventFlow x = theorySelfClassifierToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      theorySelfClassifierFromEventFlow (theorySelfClassifierToEventFlow x) =
        theorySelfClassifierFromEventFlow (theorySelfClassifierToEventFlow y) :=
    congrArg theorySelfClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (theorySelfClassifier_round_trip x).symm
      (Eq.trans hread (theorySelfClassifier_round_trip y)))

private theorem TheorySelfClassifierTasteGate_single_carrier_alignment_field_faithful :
    forall x y : TheorySelfClassifierUp,
      theorySelfClassifierFields x = theorySelfClassifierFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk generator equality recursor purity boundary ledger transport route provenance name =>
      cases y with
      | mk generator' equality' recursor' purity' boundary' ledger' transport' route'
          provenance' name' =>
          change
            [generator, equality, recursor, purity, boundary, ledger, transport, route,
                provenance, name] =
              [generator', equality', recursor', purity', boundary', ledger', transport',
                route', provenance', name'] at hfields
          injection hfields with hGenerator hTail0
          injection hTail0 with hEquality hTail1
          injection hTail1 with hRecursor hTail2
          injection hTail2 with hPurity hTail3
          injection hTail3 with hBoundary hTail4
          injection hTail4 with hLedger hTail5
          injection hTail5 with hTransport hTail6
          injection hTail6 with hRoute hTail7
          injection hTail7 with hProvenance hTail8
          injection hTail8 with hName _hNil
          cases hGenerator
          cases hEquality
          cases hRecursor
          cases hPurity
          cases hBoundary
          cases hLedger
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance theorySelfClassifierBHistCarrier : BHistCarrier TheorySelfClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := theorySelfClassifierToEventFlow
  fromEventFlow := theorySelfClassifierFromEventFlow

instance theorySelfClassifierChapterTasteGate :
    ChapterTasteGate TheorySelfClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change theorySelfClassifierFromEventFlow (theorySelfClassifierToEventFlow x) = some x
    exact theorySelfClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (theorySelfClassifierToEventFlow_injective heq)

instance theorySelfClassifierFieldFaithful :
    FieldFaithful TheorySelfClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := theorySelfClassifierFields
  field_faithful := TheorySelfClassifierTasteGate_single_carrier_alignment_field_faithful

instance theorySelfClassifierNontrivial : Nontrivial TheorySelfClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TheorySelfClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TheorySelfClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TheorySelfClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  theorySelfClassifierChapterTasteGate

theorem TheorySelfClassifierTasteGate_single_carrier_alignment :
    (forall h : BHist,
      theorySelfClassifierDecodeBHist (theorySelfClassifierEncodeBHist h) = h) ∧
      (forall x : TheorySelfClassifierUp,
        theorySelfClassifierFromEventFlow (theorySelfClassifierToEventFlow x) = some x) ∧
        (forall x y : TheorySelfClassifierUp,
          theorySelfClassifierToEventFlow x = theorySelfClassifierToEventFlow y -> x = y) ∧
          theorySelfClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact theorySelfClassifier_decode_encode_bhist
  · constructor
    · exact theorySelfClassifier_round_trip
    · constructor
      · intro x y heq
        exact theorySelfClassifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.TheorySelfClassifierUp

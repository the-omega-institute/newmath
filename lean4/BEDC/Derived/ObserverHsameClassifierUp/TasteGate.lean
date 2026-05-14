import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverHsameClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverHsameClassifierUp : Type where
  | mk :
      (leftHistory rightHistory licensed transport ledger decision route provenance name : BHist) →
      ObserverHsameClassifierUp
  deriving DecidableEq

private def observerHsameClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerHsameClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerHsameClassifierEncodeBHist h

private def observerHsameClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerHsameClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerHsameClassifierDecodeBHist tail)

private theorem observerHsameClassifierDecode_encode_bhist :
    ∀ h : BHist,
      observerHsameClassifierDecodeBHist (observerHsameClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observerHsameClassifier_mk_congr
    {leftHistory leftHistory' rightHistory rightHistory' licensed licensed' transport
      transport' ledger ledger' decision decision' route route' provenance provenance'
      name name' : BHist}
    (hLeftHistory : leftHistory' = leftHistory)
    (hRightHistory : rightHistory' = rightHistory)
    (hLicensed : licensed' = licensed)
    (hTransport : transport' = transport)
    (hLedger : ledger' = ledger)
    (hDecision : decision' = decision)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ObserverHsameClassifierUp.mk leftHistory' rightHistory' licensed' transport' ledger'
        decision' route' provenance' name' =
      ObserverHsameClassifierUp.mk leftHistory rightHistory licensed transport ledger
        decision route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLeftHistory
  cases hRightHistory
  cases hLicensed
  cases hTransport
  cases hLedger
  cases hDecision
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def observerHsameClassifierToEventFlow : ObserverHsameClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverHsameClassifierUp.mk leftHistory rightHistory licensed transport ledger
      decision route provenance name =>
      [[BMark.b0],
        observerHsameClassifierEncodeBHist leftHistory,
        [BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist rightHistory,
        [BMark.b1, BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist licensed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerHsameClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerHsameClassifierEncodeBHist name]

private def observerHsameClassifierFromEventFlow : EventFlow → Option ObserverHsameClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftHistory :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightHistory :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | licensed :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | decision :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ObserverHsameClassifierUp.mk
                                                                                  (observerHsameClassifierDecodeBHist leftHistory)
                                                                                  (observerHsameClassifierDecodeBHist rightHistory)
                                                                                  (observerHsameClassifierDecodeBHist licensed)
                                                                                  (observerHsameClassifierDecodeBHist transport)
                                                                                  (observerHsameClassifierDecodeBHist ledger)
                                                                                  (observerHsameClassifierDecodeBHist decision)
                                                                                  (observerHsameClassifierDecodeBHist route)
                                                                                  (observerHsameClassifierDecodeBHist provenance)
                                                                                  (observerHsameClassifierDecodeBHist name))
                                                                          | _ :: _ => none

private theorem observerHsameClassifier_round_trip :
    ∀ x : ObserverHsameClassifierUp,
      observerHsameClassifierFromEventFlow (observerHsameClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftHistory rightHistory licensed transport ledger decision route provenance name =>
      change
        some
          (ObserverHsameClassifierUp.mk
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist leftHistory))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist rightHistory))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist licensed))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist transport))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist ledger))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist decision))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist route))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist provenance))
            (observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist name))) =
          some
            (ObserverHsameClassifierUp.mk leftHistory rightHistory licensed transport
              ledger decision route provenance name)
      exact
        congrArg some
          (observerHsameClassifier_mk_congr
            (observerHsameClassifierDecode_encode_bhist leftHistory)
            (observerHsameClassifierDecode_encode_bhist rightHistory)
            (observerHsameClassifierDecode_encode_bhist licensed)
            (observerHsameClassifierDecode_encode_bhist transport)
            (observerHsameClassifierDecode_encode_bhist ledger)
            (observerHsameClassifierDecode_encode_bhist decision)
            (observerHsameClassifierDecode_encode_bhist route)
            (observerHsameClassifierDecode_encode_bhist provenance)
            (observerHsameClassifierDecode_encode_bhist name))

private theorem observerHsameClassifierToEventFlow_injective
    {x y : ObserverHsameClassifierUp} :
    observerHsameClassifierToEventFlow x = observerHsameClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerHsameClassifierFromEventFlow (observerHsameClassifierToEventFlow x) =
        observerHsameClassifierFromEventFlow (observerHsameClassifierToEventFlow y) :=
    congrArg observerHsameClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerHsameClassifier_round_trip x).symm
      (Eq.trans hread (observerHsameClassifier_round_trip y)))

private def observerHsameClassifierFields : ObserverHsameClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverHsameClassifierUp.mk leftHistory rightHistory licensed transport ledger
      decision route provenance name =>
      [leftHistory, rightHistory, licensed, transport, ledger, decision, route, provenance,
        name]

private theorem observerHsameClassifier_field_faithful :
    ∀ x y : ObserverHsameClassifierUp,
      observerHsameClassifierFields x = observerHsameClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk leftHistory1 rightHistory1 licensed1 transport1 ledger1 decision1 route1 provenance1
      name1 =>
      cases y with
      | mk leftHistory2 rightHistory2 licensed2 transport2 ledger2 decision2 route2
          provenance2 name2 =>
          injection h with hLeftHistory t1
          injection t1 with hRightHistory t2
          injection t2 with hLicensed t3
          injection t3 with hTransport t4
          injection t4 with hLedger t5
          injection t5 with hDecision t6
          injection t6 with hRoute t7
          injection t7 with hProvenance t8
          injection t8 with hName _
          cases hLeftHistory
          cases hRightHistory
          cases hLicensed
          cases hTransport
          cases hLedger
          cases hDecision
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance observerHsameClassifierBHistCarrier : BHistCarrier ObserverHsameClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerHsameClassifierToEventFlow
  fromEventFlow := observerHsameClassifierFromEventFlow

instance observerHsameClassifierChapterTasteGate :
    ChapterTasteGate ObserverHsameClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerHsameClassifierFromEventFlow (observerHsameClassifierToEventFlow x) =
      some x
    exact observerHsameClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerHsameClassifierToEventFlow_injective heq)

instance observerHsameClassifierFieldFaithful : FieldFaithful ObserverHsameClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerHsameClassifierFields
  field_faithful := observerHsameClassifier_field_faithful

instance observerHsameClassifierNontrivial : Nontrivial ObserverHsameClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverHsameClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverHsameClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverHsameClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerHsameClassifierChapterTasteGate

theorem ObserverHsameClassifierTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ObserverHsameClassifierUp) ∧
      Nonempty (FieldFaithful ObserverHsameClassifierUp) ∧
      Nonempty (Nontrivial ObserverHsameClassifierUp) ∧
        (∀ h : BHist,
          observerHsameClassifierDecodeBHist
              (observerHsameClassifierEncodeBHist h) =
            h) ∧
          observerHsameClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨observerHsameClassifierChapterTasteGate⟩,
      ⟨observerHsameClassifierFieldFaithful⟩,
      ⟨observerHsameClassifierNontrivial⟩,
      observerHsameClassifierDecode_encode_bhist, rfl⟩

end BEDC.Derived.ObserverHsameClassifierUp

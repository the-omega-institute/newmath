import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosurePreservationClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosurePreservationClassifierUp : Type where
  | mk :
      (closedAt shift subst beta betaStar transport routes provenance name : BHist) →
      ClosurePreservationClassifierUp
  deriving DecidableEq

def closurePreservationClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closurePreservationClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closurePreservationClassifierEncodeBHist h

def closurePreservationClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closurePreservationClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closurePreservationClassifierDecodeBHist tail)

private theorem closurePreservationClassifier_decode_encode_bhist :
    ∀ h : BHist,
      closurePreservationClassifierDecodeBHist
        (closurePreservationClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closurePreservationClassifierToEventFlow :
    ClosurePreservationClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosurePreservationClassifierUp.mk closedAt shift subst beta betaStar transport
      routes provenance name =>
      [[BMark.b0],
        closurePreservationClassifierEncodeBHist closedAt,
        [BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist subst,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist beta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist betaStar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closurePreservationClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closurePreservationClassifierEncodeBHist name]

def closurePreservationClassifierFromEventFlow :
    EventFlow → Option ClosurePreservationClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | closedAt :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | shift :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | subst :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | beta :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | betaStar :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | name ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (ClosurePreservationClassifierUp.mk
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    closedAt)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    shift)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    subst)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    beta)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    betaStar)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    transport)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    routes)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    provenance)
                                                                                  (closurePreservationClassifierDecodeBHist
                                                                                    name))
                                                                          | _ :: _ =>
                                                                              none

private theorem closurePreservationClassifier_round_trip :
    ∀ x : ClosurePreservationClassifierUp,
      closurePreservationClassifierFromEventFlow
        (closurePreservationClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedAt shift subst beta betaStar transport routes provenance name =>
      change
        some
          (ClosurePreservationClassifierUp.mk
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist closedAt))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist shift))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist subst))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist beta))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist betaStar))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist transport))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist routes))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist provenance))
            (closurePreservationClassifierDecodeBHist
              (closurePreservationClassifierEncodeBHist name))) =
          some
            (ClosurePreservationClassifierUp.mk closedAt shift subst beta betaStar
              transport routes provenance name)
      rw [closurePreservationClassifier_decode_encode_bhist closedAt,
        closurePreservationClassifier_decode_encode_bhist shift,
        closurePreservationClassifier_decode_encode_bhist subst,
        closurePreservationClassifier_decode_encode_bhist beta,
        closurePreservationClassifier_decode_encode_bhist betaStar,
        closurePreservationClassifier_decode_encode_bhist transport,
        closurePreservationClassifier_decode_encode_bhist routes,
        closurePreservationClassifier_decode_encode_bhist provenance,
        closurePreservationClassifier_decode_encode_bhist name]

private theorem closurePreservationClassifierToEventFlow_injective
    {x y : ClosurePreservationClassifierUp} :
    closurePreservationClassifierToEventFlow x =
      closurePreservationClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closurePreservationClassifierFromEventFlow
          (closurePreservationClassifierToEventFlow x) =
        closurePreservationClassifierFromEventFlow
          (closurePreservationClassifierToEventFlow y) :=
    congrArg closurePreservationClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closurePreservationClassifier_round_trip x).symm
      (Eq.trans hread (closurePreservationClassifier_round_trip y)))

instance closurePreservationClassifierBHistCarrier :
    BHistCarrier ClosurePreservationClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closurePreservationClassifierToEventFlow
  fromEventFlow := closurePreservationClassifierFromEventFlow

instance closurePreservationClassifierChapterTasteGate :
    ChapterTasteGate ClosurePreservationClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closurePreservationClassifierFromEventFlow
        (closurePreservationClassifierToEventFlow x) = some x
    exact closurePreservationClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closurePreservationClassifierToEventFlow_injective heq)

instance closurePreservationClassifierFieldFaithful :
    FieldFaithful ClosurePreservationClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ClosurePreservationClassifierUp.mk closedAt shift subst beta betaStar transport
        routes provenance name =>
        [closedAt, shift, subst, beta, betaStar, transport, routes, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk closedAt1 shift1 subst1 beta1 betaStar1 transport1 routes1 provenance1
        name1 =>
        cases y with
        | mk closedAt2 shift2 subst2 beta2 betaStar2 transport2 routes2 provenance2
            name2 =>
            injection h with hClosedAt t1
            injection t1 with hShift t2
            injection t2 with hSubst t3
            injection t3 with hBeta t4
            injection t4 with hBetaStar t5
            injection t5 with hTransport t6
            injection t6 with hRoutes t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hClosedAt
            cases hShift
            cases hSubst
            cases hBeta
            cases hBetaStar
            cases hTransport
            cases hRoutes
            cases hProvenance
            cases hName
            rfl

theorem ClosurePreservationClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closurePreservationClassifierDecodeBHist
        (closurePreservationClassifierEncodeBHist h) = h) ∧
      (∀ x : ClosurePreservationClassifierUp,
        closurePreservationClassifierFromEventFlow
          (closurePreservationClassifierToEventFlow x) = some x) ∧
        (∀ x y : ClosurePreservationClassifierUp,
          closurePreservationClassifierToEventFlow x =
            closurePreservationClassifierToEventFlow y → x = y) ∧
          closurePreservationClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closurePreservationClassifier_decode_encode_bhist
  · constructor
    · exact closurePreservationClassifier_round_trip
    · constructor
      · intro x y heq
        exact closurePreservationClassifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosurePreservationClassifierUp

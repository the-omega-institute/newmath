import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverLicensedComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverLicensedComparisonUp : Type where
  | mk (history sourceLedger transport classifier routes provenance name : BHist) :
      ObserverLicensedComparisonUp
  deriving DecidableEq

def observerLicensedComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerLicensedComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerLicensedComparisonEncodeBHist h

def observerLicensedComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerLicensedComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerLicensedComparisonDecodeBHist tail)

private theorem observerLicensedComparisonDecode_encode_bhist :
    ∀ h : BHist,
      observerLicensedComparisonDecodeBHist (observerLicensedComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerLicensedComparisonToEventFlow : ObserverLicensedComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverLicensedComparisonUp.mk history sourceLedger transport classifier routes provenance
      name =>
      [[BMark.b0],
        observerLicensedComparisonEncodeBHist history,
        [BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist sourceLedger,
        [BMark.b1, BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLicensedComparisonEncodeBHist name]

def observerLicensedComparisonFromEventFlow : EventFlow → Option ObserverLicensedComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routes :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (ObserverLicensedComparisonUp.mk
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    history)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    sourceLedger)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    transport)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    classifier)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    routes)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    provenance)
                                                                  (observerLicensedComparisonDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem observerLicensedComparison_round_trip :
    ∀ x : ObserverLicensedComparisonUp,
      observerLicensedComparisonFromEventFlow (observerLicensedComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history sourceLedger transport classifier routes provenance name =>
      change
        some
          (ObserverLicensedComparisonUp.mk
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist history))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist sourceLedger))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist transport))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist classifier))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist routes))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist provenance))
            (observerLicensedComparisonDecodeBHist
              (observerLicensedComparisonEncodeBHist name))) =
          some
            (ObserverLicensedComparisonUp.mk history sourceLedger transport classifier routes
              provenance name)
      rw [observerLicensedComparisonDecode_encode_bhist history,
        observerLicensedComparisonDecode_encode_bhist sourceLedger,
        observerLicensedComparisonDecode_encode_bhist transport,
        observerLicensedComparisonDecode_encode_bhist classifier,
        observerLicensedComparisonDecode_encode_bhist routes,
        observerLicensedComparisonDecode_encode_bhist provenance,
        observerLicensedComparisonDecode_encode_bhist name]

private theorem observerLicensedComparisonToEventFlow_injective
    {x y : ObserverLicensedComparisonUp} :
    observerLicensedComparisonToEventFlow x = observerLicensedComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerLicensedComparisonFromEventFlow (observerLicensedComparisonToEventFlow x) =
        observerLicensedComparisonFromEventFlow (observerLicensedComparisonToEventFlow y) :=
    congrArg observerLicensedComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerLicensedComparison_round_trip x).symm
      (Eq.trans hread (observerLicensedComparison_round_trip y)))

def observerLicensedComparisonFields : ObserverLicensedComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverLicensedComparisonUp.mk history sourceLedger transport classifier routes provenance
      name =>
      [history, sourceLedger, transport, classifier, routes, provenance, name]

private theorem observerLicensedComparison_field_faithful :
    ∀ x y : ObserverLicensedComparisonUp,
      observerLicensedComparisonFields x = observerLicensedComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk history sourceLedger transport classifier routes provenance name =>
      cases y with
      | mk history' sourceLedger' transport' classifier' routes' provenance' name' =>
          cases hfields
          rfl

instance observerLicensedComparisonBHistCarrier : BHistCarrier ObserverLicensedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerLicensedComparisonToEventFlow
  fromEventFlow := observerLicensedComparisonFromEventFlow

instance observerLicensedComparisonChapterTasteGate :
    ChapterTasteGate ObserverLicensedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerLicensedComparisonFromEventFlow (observerLicensedComparisonToEventFlow x) =
        some x
    exact observerLicensedComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerLicensedComparisonToEventFlow_injective heq)

instance observerLicensedComparisonFieldFaithful :
    FieldFaithful ObserverLicensedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerLicensedComparisonFields
  field_faithful := observerLicensedComparison_field_faithful

instance observerLicensedComparisonNontrivial : Nontrivial ObserverLicensedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverLicensedComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObserverLicensedComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverLicensedComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerLicensedComparisonChapterTasteGate

theorem ObserverLicensedComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerLicensedComparisonDecodeBHist (observerLicensedComparisonEncodeBHist h) = h) ∧
      (∀ x : ObserverLicensedComparisonUp,
        observerLicensedComparisonFromEventFlow (observerLicensedComparisonToEventFlow x) =
          some x) ∧
        (∀ x y : ObserverLicensedComparisonUp,
          observerLicensedComparisonToEventFlow x =
            observerLicensedComparisonToEventFlow y → x = y) ∧
          observerLicensedComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨observerLicensedComparisonDecode_encode_bhist,
      observerLicensedComparison_round_trip,
      (fun _ _ heq => observerLicensedComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ObserverLicensedComparisonUp

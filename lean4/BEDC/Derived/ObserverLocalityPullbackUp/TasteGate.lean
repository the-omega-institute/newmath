import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverLocalityPullbackUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverLocalityPullbackUp : Type where
  | mk
      (observer causal rate transport compatibility hsameRow probeRow route provenance
        name : BHist) :
      ObserverLocalityPullbackUp
  deriving DecidableEq

def observerLocalityPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerLocalityPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerLocalityPullbackEncodeBHist h

def observerLocalityPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerLocalityPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerLocalityPullbackDecodeBHist tail)

private theorem observerLocalityPullback_decode_encode_bhist :
    ∀ h : BHist,
      observerLocalityPullbackDecodeBHist (observerLocalityPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerLocalityPullbackToEventFlow : ObserverLocalityPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverLocalityPullbackUp.mk observer causal rate transport compatibility hsameRow probeRow
      route provenance name =>
      [[BMark.b0],
        observerLocalityPullbackEncodeBHist observer,
        [BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist causal,
        [BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist rate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist compatibility,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist hsameRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist probeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerLocalityPullbackEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerLocalityPullbackEncodeBHist name]

def observerLocalityPullbackFromEventFlow : EventFlow → Option ObserverLocalityPullbackUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observer :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | causal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | rate :: rest5 =>
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
                                      | compatibility :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | hsameRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | probeRow :: rest13 =>
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
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ObserverLocalityPullbackUp.mk
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            observer)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            causal)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            rate)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            transport)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            compatibility)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            hsameRow)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            probeRow)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            route)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            provenance)
                                                                                          (observerLocalityPullbackDecodeBHist
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem observerLocalityPullback_round_trip :
    ∀ x : ObserverLocalityPullbackUp,
      observerLocalityPullbackFromEventFlow
        (observerLocalityPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer causal rate transport compatibility hsameRow probeRow route provenance name =>
      change
        some
          (ObserverLocalityPullbackUp.mk
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist observer))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist causal))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist rate))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist transport))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist compatibility))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist hsameRow))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist probeRow))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist route))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist provenance))
            (observerLocalityPullbackDecodeBHist
              (observerLocalityPullbackEncodeBHist name))) =
          some
            (ObserverLocalityPullbackUp.mk observer causal rate transport compatibility
              hsameRow probeRow route provenance name)
      rw [observerLocalityPullback_decode_encode_bhist observer,
        observerLocalityPullback_decode_encode_bhist causal,
        observerLocalityPullback_decode_encode_bhist rate,
        observerLocalityPullback_decode_encode_bhist transport,
        observerLocalityPullback_decode_encode_bhist compatibility,
        observerLocalityPullback_decode_encode_bhist hsameRow,
        observerLocalityPullback_decode_encode_bhist probeRow,
        observerLocalityPullback_decode_encode_bhist route,
        observerLocalityPullback_decode_encode_bhist provenance,
        observerLocalityPullback_decode_encode_bhist name]

private theorem observerLocalityPullbackToEventFlow_injective
    {x y : ObserverLocalityPullbackUp} :
    observerLocalityPullbackToEventFlow x = observerLocalityPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerLocalityPullbackFromEventFlow (observerLocalityPullbackToEventFlow x) =
        observerLocalityPullbackFromEventFlow (observerLocalityPullbackToEventFlow y) :=
    congrArg observerLocalityPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerLocalityPullback_round_trip x).symm
      (Eq.trans hread (observerLocalityPullback_round_trip y)))

instance observerLocalityPullbackBHistCarrier :
    BHistCarrier ObserverLocalityPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerLocalityPullbackToEventFlow
  fromEventFlow := observerLocalityPullbackFromEventFlow

instance observerLocalityPullbackChapterTasteGate :
    ChapterTasteGate ObserverLocalityPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerLocalityPullbackFromEventFlow
        (observerLocalityPullbackToEventFlow x) = some x
    exact observerLocalityPullback_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerLocalityPullbackToEventFlow_injective heq)

instance observerLocalityPullbackFieldFaithful :
    FieldFaithful ObserverLocalityPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverLocalityPullbackUp.mk observer causal rate transport compatibility hsameRow
        probeRow route provenance name =>
        [observer, causal, rate, transport, compatibility, hsameRow, probeRow, route,
          provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk observer causal rate transport compatibility hsameRow probeRow route provenance name =>
        cases y with
        | mk observer' causal' rate' transport' compatibility' hsameRow' probeRow' route'
            provenance' name' =>
            cases hfields
            rfl

instance observerLocalityPullbackNontrivial : Nontrivial ObserverLocalityPullbackUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨ObserverLocalityPullbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverLocalityPullbackUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverLocalityPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem ObserverLocalityPullbackTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerLocalityPullbackDecodeBHist (observerLocalityPullbackEncodeBHist h) = h) ∧
      (∀ x : ObserverLocalityPullbackUp,
        observerLocalityPullbackFromEventFlow
          (observerLocalityPullbackToEventFlow x) = some x) ∧
        (∀ x y : ObserverLocalityPullbackUp,
          observerLocalityPullbackToEventFlow x =
            observerLocalityPullbackToEventFlow y → x = y) ∧
          observerLocalityPullbackEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerLocalityPullback_decode_encode_bhist
  · constructor
    · exact observerLocalityPullback_round_trip
    · constructor
      · intro x y heq
        exact observerLocalityPullbackToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverLocalityPullbackUp

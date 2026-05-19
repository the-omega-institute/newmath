import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverRegularUp : Type where
  | mk :
      (alphabet resolvingState schedule window readback transport route provenance name : BHist) →
        ObserverRegularUp
  deriving DecidableEq

def observerRegularEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerRegularEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerRegularEncodeBHist h

def observerRegularDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerRegularDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerRegularDecodeBHist tail)

private theorem observerRegularDecode_encode_bhist :
    ∀ h : BHist, observerRegularDecodeBHist (observerRegularEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerRegularToEventFlow : ObserverRegularUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverRegularUp.mk alphabet resolvingState schedule window readback transport route
      provenance name =>
      [[BMark.b0],
        observerRegularEncodeBHist alphabet,
        [BMark.b1, BMark.b0],
        observerRegularEncodeBHist resolvingState,
        [BMark.b1, BMark.b1, BMark.b0],
        observerRegularEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerRegularEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerRegularEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerRegularEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerRegularEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerRegularEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerRegularEncodeBHist name]

def observerRegularFromEventFlow : EventFlow → Option ObserverRegularUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | alphabet :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | resolvingState :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | schedule :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | window :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
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
                                                                                (ObserverRegularUp.mk
                                                                                  (observerRegularDecodeBHist
                                                                                    alphabet)
                                                                                  (observerRegularDecodeBHist
                                                                                    resolvingState)
                                                                                  (observerRegularDecodeBHist
                                                                                    schedule)
                                                                                  (observerRegularDecodeBHist
                                                                                    window)
                                                                                  (observerRegularDecodeBHist
                                                                                    readback)
                                                                                  (observerRegularDecodeBHist
                                                                                    transport)
                                                                                  (observerRegularDecodeBHist
                                                                                    route)
                                                                                  (observerRegularDecodeBHist
                                                                                    provenance)
                                                                                  (observerRegularDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem observerRegular_round_trip :
    ∀ x : ObserverRegularUp,
      observerRegularFromEventFlow (observerRegularToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk alphabet resolvingState schedule window readback transport route provenance name =>
      change
        some
          (ObserverRegularUp.mk
            (observerRegularDecodeBHist (observerRegularEncodeBHist alphabet))
            (observerRegularDecodeBHist (observerRegularEncodeBHist resolvingState))
            (observerRegularDecodeBHist (observerRegularEncodeBHist schedule))
            (observerRegularDecodeBHist (observerRegularEncodeBHist window))
            (observerRegularDecodeBHist (observerRegularEncodeBHist readback))
            (observerRegularDecodeBHist (observerRegularEncodeBHist transport))
            (observerRegularDecodeBHist (observerRegularEncodeBHist route))
            (observerRegularDecodeBHist (observerRegularEncodeBHist provenance))
            (observerRegularDecodeBHist (observerRegularEncodeBHist name))) =
          some
            (ObserverRegularUp.mk alphabet resolvingState schedule window readback transport route
              provenance name)
      rw [observerRegularDecode_encode_bhist alphabet,
        observerRegularDecode_encode_bhist resolvingState,
        observerRegularDecode_encode_bhist schedule,
        observerRegularDecode_encode_bhist window,
        observerRegularDecode_encode_bhist readback,
        observerRegularDecode_encode_bhist transport,
        observerRegularDecode_encode_bhist route,
        observerRegularDecode_encode_bhist provenance,
        observerRegularDecode_encode_bhist name]

private theorem observerRegularToEventFlow_injective {x y : ObserverRegularUp} :
    observerRegularToEventFlow x = observerRegularToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerRegularFromEventFlow (observerRegularToEventFlow x) =
        observerRegularFromEventFlow (observerRegularToEventFlow y) :=
    congrArg observerRegularFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerRegular_round_trip x).symm
      (Eq.trans hread (observerRegular_round_trip y)))

def observerRegularFields : ObserverRegularUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverRegularUp.mk alphabet resolvingState schedule window readback transport route
      provenance name =>
      [alphabet, resolvingState, schedule, window, readback, transport, route, provenance,
        name]

private theorem observerRegular_field_faithful :
    ∀ x y : ObserverRegularUp,
      observerRegularFields x = observerRegularFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk alphabet₁ resolvingState₁ schedule₁ window₁ readback₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk alphabet₂ resolvingState₂ schedule₂ window₂ readback₂ transport₂ route₂
          provenance₂ name₂ =>
          cases h
          rfl

instance observerRegularBHistCarrier : BHistCarrier ObserverRegularUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerRegularToEventFlow
  fromEventFlow := observerRegularFromEventFlow

instance observerRegularChapterTasteGate : ChapterTasteGate ObserverRegularUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerRegularFromEventFlow (observerRegularToEventFlow x) = some x
    exact observerRegular_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerRegularToEventFlow_injective heq)

instance observerRegularFieldFaithful : FieldFaithful ObserverRegularUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerRegularFields
  field_faithful := observerRegular_field_faithful

def taste_gate : ChapterTasteGate ObserverRegularUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerRegularChapterTasteGate

theorem ObserverRegularTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerRegularDecodeBHist (observerRegularEncodeBHist h) = h) ∧
      (∀ x : ObserverRegularUp,
        observerRegularFromEventFlow (observerRegularToEventFlow x) = some x) ∧
        (∀ x y : ObserverRegularUp, observerRegularToEventFlow x = observerRegularToEventFlow y →
          x = y) ∧
          observerRegularEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerRegularDecode_encode_bhist
  · constructor
    · exact observerRegular_round_trip
    · constructor
      · intro x y heq
        exact observerRegularToEventFlow_injective heq
      · rfl

theorem ObserverRegularTasteGate_visible_rows :
    exists x : ObserverRegularUp,
      x =
          ObserverRegularUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  refine
    Exists.intro
      (ObserverRegularUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
      (And.intro rfl ?rt)
  change
    observerRegularFromEventFlow
        (observerRegularToEventFlow
          (ObserverRegularUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (ObserverRegularUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
  exact
    observerRegular_round_trip
      (ObserverRegularUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived.ObserverRegularUp

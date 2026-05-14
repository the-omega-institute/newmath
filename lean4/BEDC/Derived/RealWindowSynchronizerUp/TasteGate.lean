import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealWindowSynchronizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealWindowSynchronizerUp : Type where
  | mk :
      (window tail threshold limitSeal realSeal transport routes provenance name : BHist) →
      RealWindowSynchronizerUp
  deriving DecidableEq

def realWindowSynchronizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realWindowSynchronizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realWindowSynchronizerEncodeBHist h

def realWindowSynchronizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realWindowSynchronizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realWindowSynchronizerDecodeBHist tail)

private theorem realWindowSynchronizerDecode_encode_bhist :
    ∀ h : BHist,
      realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realWindowSynchronizerToEventFlow : RealWindowSynchronizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealWindowSynchronizerUp.mk window tail threshold limitSeal realSeal transport routes
      provenance name =>
      [[BMark.b0],
        realWindowSynchronizerEncodeBHist window,
        [BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist threshold,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realWindowSynchronizerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realWindowSynchronizerEncodeBHist name]

def realWindowSynchronizerFromEventFlow : EventFlow → Option RealWindowSynchronizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | tail :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | threshold :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | limitSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
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
                                                                                (RealWindowSynchronizerUp.mk
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    window)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    tail)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    threshold)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    limitSeal)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    realSeal)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    transport)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    routes)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    provenance)
                                                                                  (realWindowSynchronizerDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem realWindowSynchronizer_round_trip :
    ∀ x : RealWindowSynchronizerUp,
      realWindowSynchronizerFromEventFlow (realWindowSynchronizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window tail threshold limitSeal realSeal transport routes provenance name =>
      change
        some
          (RealWindowSynchronizerUp.mk
            (realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist window))
            (realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist tail))
            (realWindowSynchronizerDecodeBHist
              (realWindowSynchronizerEncodeBHist threshold))
            (realWindowSynchronizerDecodeBHist
              (realWindowSynchronizerEncodeBHist limitSeal))
            (realWindowSynchronizerDecodeBHist
              (realWindowSynchronizerEncodeBHist realSeal))
            (realWindowSynchronizerDecodeBHist
              (realWindowSynchronizerEncodeBHist transport))
            (realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist routes))
            (realWindowSynchronizerDecodeBHist
              (realWindowSynchronizerEncodeBHist provenance))
            (realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist name))) =
          some
            (RealWindowSynchronizerUp.mk window tail threshold limitSeal realSeal transport
              routes provenance name)
      rw [realWindowSynchronizerDecode_encode_bhist window,
        realWindowSynchronizerDecode_encode_bhist tail,
        realWindowSynchronizerDecode_encode_bhist threshold,
        realWindowSynchronizerDecode_encode_bhist limitSeal,
        realWindowSynchronizerDecode_encode_bhist realSeal,
        realWindowSynchronizerDecode_encode_bhist transport,
        realWindowSynchronizerDecode_encode_bhist routes,
        realWindowSynchronizerDecode_encode_bhist provenance,
        realWindowSynchronizerDecode_encode_bhist name]

private theorem realWindowSynchronizerToEventFlow_injective {x y : RealWindowSynchronizerUp} :
    realWindowSynchronizerToEventFlow x = realWindowSynchronizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realWindowSynchronizerFromEventFlow (realWindowSynchronizerToEventFlow x) =
        realWindowSynchronizerFromEventFlow (realWindowSynchronizerToEventFlow y) :=
    congrArg realWindowSynchronizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realWindowSynchronizer_round_trip x).symm
      (Eq.trans hread (realWindowSynchronizer_round_trip y)))

instance realWindowSynchronizerBHistCarrier : BHistCarrier RealWindowSynchronizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realWindowSynchronizerToEventFlow
  fromEventFlow := realWindowSynchronizerFromEventFlow

instance realWindowSynchronizerChapterTasteGate : ChapterTasteGate RealWindowSynchronizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realWindowSynchronizerFromEventFlow (realWindowSynchronizerToEventFlow x) = some x
    exact realWindowSynchronizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realWindowSynchronizerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealWindowSynchronizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realWindowSynchronizerChapterTasteGate

instance realWindowSynchronizerFieldFaithful : FieldFaithful RealWindowSynchronizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealWindowSynchronizerUp.mk window tail threshold limitSeal realSeal transport routes
        provenance name =>
        [window, tail, threshold, limitSeal, realSeal, transport, routes, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk window₁ tail₁ threshold₁ limitSeal₁ realSeal₁ transport₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk window₂ tail₂ threshold₂ limitSeal₂ realSeal₂ transport₂ routes₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

theorem RealWindowSynchronizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realWindowSynchronizerDecodeBHist (realWindowSynchronizerEncodeBHist h) = h) ∧
      (∀ x : RealWindowSynchronizerUp,
        realWindowSynchronizerFromEventFlow (realWindowSynchronizerToEventFlow x) = some x) ∧
        (∀ x y : RealWindowSynchronizerUp,
          realWindowSynchronizerToEventFlow x = realWindowSynchronizerToEventFlow y → x = y) ∧
          realWindowSynchronizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realWindowSynchronizerDecode_encode_bhist
  · constructor
    · exact realWindowSynchronizer_round_trip
    · constructor
      · intro x y heq
        exact realWindowSynchronizerToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealWindowSynchronizerUp

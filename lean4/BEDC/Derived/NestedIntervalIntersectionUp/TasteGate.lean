import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalIntersectionUp : Type where
  | mk :
      (sourceChain width selector endpoints handoff sealRow transport route name : BHist) →
      NestedIntervalIntersectionUp

def nestedIntervalIntersectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalIntersectionEncodeBHist h

def nestedIntervalIntersectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalIntersectionDecodeBHist tail)

private theorem nestedIntervalIntersectionDecode_encode_bhist :
    ∀ h : BHist,
      nestedIntervalIntersectionDecodeBHist (nestedIntervalIntersectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nestedIntervalIntersectionToEventFlow : NestedIntervalIntersectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalIntersectionUp.mk sourceChain width selector endpoints handoff sealRow
      transport route name =>
      [[BMark.b0],
        nestedIntervalIntersectionEncodeBHist sourceChain,
        [BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist width,
        [BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist endpoints,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nestedIntervalIntersectionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        nestedIntervalIntersectionEncodeBHist name]

def nestedIntervalIntersectionFromEventFlow : EventFlow → Option NestedIntervalIntersectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceChain :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | width :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selector :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | endpoints :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | handoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (NestedIntervalIntersectionUp.mk
                                                                                  (nestedIntervalIntersectionDecodeBHist sourceChain)
                                                                                  (nestedIntervalIntersectionDecodeBHist width)
                                                                                  (nestedIntervalIntersectionDecodeBHist selector)
                                                                                  (nestedIntervalIntersectionDecodeBHist endpoints)
                                                                                  (nestedIntervalIntersectionDecodeBHist handoff)
                                                                                  (nestedIntervalIntersectionDecodeBHist sealRow)
                                                                                  (nestedIntervalIntersectionDecodeBHist transport)
                                                                                  (nestedIntervalIntersectionDecodeBHist route)
                                                                                  (nestedIntervalIntersectionDecodeBHist name))
                                                                          | _ :: _ => none

private theorem nestedIntervalIntersection_round_trip :
    ∀ x : NestedIntervalIntersectionUp,
      nestedIntervalIntersectionFromEventFlow
        (nestedIntervalIntersectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceChain width selector endpoints handoff sealRow transport route name =>
      change
        some
          (NestedIntervalIntersectionUp.mk
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist sourceChain))
            (nestedIntervalIntersectionDecodeBHist (nestedIntervalIntersectionEncodeBHist width))
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist selector))
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist endpoints))
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist handoff))
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist sealRow))
            (nestedIntervalIntersectionDecodeBHist
              (nestedIntervalIntersectionEncodeBHist transport))
            (nestedIntervalIntersectionDecodeBHist (nestedIntervalIntersectionEncodeBHist route))
            (nestedIntervalIntersectionDecodeBHist (nestedIntervalIntersectionEncodeBHist name))) =
          some
            (NestedIntervalIntersectionUp.mk sourceChain width selector endpoints handoff sealRow
              transport route name)
      rw [nestedIntervalIntersectionDecode_encode_bhist sourceChain,
        nestedIntervalIntersectionDecode_encode_bhist width,
        nestedIntervalIntersectionDecode_encode_bhist selector,
        nestedIntervalIntersectionDecode_encode_bhist endpoints,
        nestedIntervalIntersectionDecode_encode_bhist handoff,
        nestedIntervalIntersectionDecode_encode_bhist sealRow,
        nestedIntervalIntersectionDecode_encode_bhist transport,
        nestedIntervalIntersectionDecode_encode_bhist route,
        nestedIntervalIntersectionDecode_encode_bhist name]

private theorem nestedIntervalIntersectionToEventFlow_injective
    {x y : NestedIntervalIntersectionUp} :
    nestedIntervalIntersectionToEventFlow x =
      nestedIntervalIntersectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalIntersectionFromEventFlow
          (nestedIntervalIntersectionToEventFlow x) =
        nestedIntervalIntersectionFromEventFlow
          (nestedIntervalIntersectionToEventFlow y) :=
    congrArg nestedIntervalIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nestedIntervalIntersection_round_trip x).symm
      (Eq.trans hread (nestedIntervalIntersection_round_trip y)))

instance nestedIntervalIntersectionBHistCarrier :
    BHistCarrier NestedIntervalIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalIntersectionToEventFlow
  fromEventFlow := nestedIntervalIntersectionFromEventFlow

instance nestedIntervalIntersectionChapterTasteGate :
    ChapterTasteGate NestedIntervalIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalIntersectionFromEventFlow
        (nestedIntervalIntersectionToEventFlow x) = some x
    exact nestedIntervalIntersection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalIntersectionToEventFlow_injective heq)

theorem NestedIntervalIntersectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalIntersectionDecodeBHist (nestedIntervalIntersectionEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalIntersectionUp,
        nestedIntervalIntersectionFromEventFlow
          (nestedIntervalIntersectionToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalIntersectionUp,
          nestedIntervalIntersectionToEventFlow x =
            nestedIntervalIntersectionToEventFlow y → x = y) ∧
          nestedIntervalIntersectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nestedIntervalIntersectionDecode_encode_bhist
  · constructor
    · exact nestedIntervalIntersection_round_trip
    · constructor
      · intro x y heq
        exact nestedIntervalIntersectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.NestedIntervalIntersectionUp

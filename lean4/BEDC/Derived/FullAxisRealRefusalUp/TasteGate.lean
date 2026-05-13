import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FullAxisRealRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FullAxisRealRefusalUp : Type where
  | mk : (fullAxis refusal cannotClaim transport route provenance name : BHist) →
      FullAxisRealRefusalUp
  deriving DecidableEq

def fullAxisRealRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fullAxisRealRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fullAxisRealRefusalEncodeBHist h

def fullAxisRealRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fullAxisRealRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fullAxisRealRefusalDecodeBHist tail)

private theorem fullAxisRealRefusalDecode_encode_bhist :
    ∀ h : BHist, fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fullAxisRealRefusalToEventFlow : FullAxisRealRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance name =>
      [[BMark.b0],
        fullAxisRealRefusalEncodeBHist fullAxis,
        [BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisRealRefusalEncodeBHist name]

def fullAxisRealRefusalFromEventFlow : EventFlow → Option FullAxisRealRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | fullAxis :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cannotClaim :: rest5 =>
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
                                      | route :: rest9 =>
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
                                                                (FullAxisRealRefusalUp.mk
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    fullAxis)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    refusal)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    cannotClaim)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    transport)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    route)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    provenance)
                                                                  (fullAxisRealRefusalDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem fullAxisRealRefusal_round_trip :
    ∀ x : FullAxisRealRefusalUp,
      fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fullAxis refusal cannotClaim transport route provenance name =>
      change
        some
          (FullAxisRealRefusalUp.mk
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist fullAxis))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist refusal))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist cannotClaim))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist transport))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist route))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist provenance))
            (fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist name))) =
          some
            (FullAxisRealRefusalUp.mk fullAxis refusal cannotClaim transport route provenance
              name)
      rw [fullAxisRealRefusalDecode_encode_bhist fullAxis,
        fullAxisRealRefusalDecode_encode_bhist refusal,
        fullAxisRealRefusalDecode_encode_bhist cannotClaim,
        fullAxisRealRefusalDecode_encode_bhist transport,
        fullAxisRealRefusalDecode_encode_bhist route,
        fullAxisRealRefusalDecode_encode_bhist provenance,
        fullAxisRealRefusalDecode_encode_bhist name]

private theorem fullAxisRealRefusalToEventFlow_injective {x y : FullAxisRealRefusalUp} :
    fullAxisRealRefusalToEventFlow x = fullAxisRealRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow x) =
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow y) :=
    congrArg fullAxisRealRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fullAxisRealRefusal_round_trip x).symm
      (Eq.trans hread (fullAxisRealRefusal_round_trip y)))

instance fullAxisRealRefusalBHistCarrier : BHistCarrier FullAxisRealRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fullAxisRealRefusalToEventFlow
  fromEventFlow := fullAxisRealRefusalFromEventFlow

instance fullAxisRealRefusalChapterTasteGate : ChapterTasteGate FullAxisRealRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow x) = some x
    exact fullAxisRealRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fullAxisRealRefusalToEventFlow_injective heq)

theorem FullAxisRealRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, fullAxisRealRefusalDecodeBHist (fullAxisRealRefusalEncodeBHist h) = h) ∧
      (∀ x : FullAxisRealRefusalUp,
        fullAxisRealRefusalFromEventFlow (fullAxisRealRefusalToEventFlow x) = some x) ∧
        (∀ x y : FullAxisRealRefusalUp,
          fullAxisRealRefusalToEventFlow x = fullAxisRealRefusalToEventFlow y → x = y) ∧
          fullAxisRealRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fullAxisRealRefusalDecode_encode_bhist
  · constructor
    · exact fullAxisRealRefusal_round_trip
    · constructor
      · intro x y heq
        exact fullAxisRealRefusalToEventFlow_injective heq
      · rfl

end BEDC.Derived.FullAxisRealRefusalUp

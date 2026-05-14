import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CriticalStripBarrierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CriticalStripBarrierUp : Type where
  | mk :
      (strip zero witness real rational approach transport route package name : BHist) →
      CriticalStripBarrierUp
  deriving DecidableEq

def criticalStripBarrierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: criticalStripBarrierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: criticalStripBarrierEncodeBHist h

def criticalStripBarrierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (criticalStripBarrierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (criticalStripBarrierDecodeBHist tail)

private theorem criticalStripBarrier_decode_encode_bhist :
    ∀ h : BHist, criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def criticalStripBarrierFields : CriticalStripBarrierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CriticalStripBarrierUp.mk strip zero witness real rational approach transport route package
      name =>
      [strip, zero, witness, real, rational, approach, transport, route, package, name]

def criticalStripBarrierToEventFlow : CriticalStripBarrierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CriticalStripBarrierUp.mk strip zero witness real rational approach transport route package
      name =>
      [[BMark.b0],
        criticalStripBarrierEncodeBHist strip,
        [BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist zero,
        [BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist rational,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist approach,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        criticalStripBarrierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        criticalStripBarrierEncodeBHist name]

def criticalStripBarrierFromEventFlow : EventFlow → Option CriticalStripBarrierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | strip :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | zero :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | witness :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | real :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | rational :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | approach :: rest11 =>
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
                                                                      | package :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (CriticalStripBarrierUp.mk
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            strip)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            zero)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            witness)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            real)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            rational)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            approach)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            transport)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            route)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            package)
                                                                                          (criticalStripBarrierDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem criticalStripBarrier_round_trip :
    ∀ x : CriticalStripBarrierUp,
      criticalStripBarrierFromEventFlow (criticalStripBarrierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk strip zero witness real rational approach transport route package name =>
      change
        some
          (CriticalStripBarrierUp.mk
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist strip))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist zero))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist witness))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist real))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist rational))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist approach))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist transport))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist route))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist package))
            (criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist name))) =
          some
            (CriticalStripBarrierUp.mk strip zero witness real rational approach transport route
              package name)
      rw [criticalStripBarrier_decode_encode_bhist strip,
        criticalStripBarrier_decode_encode_bhist zero,
        criticalStripBarrier_decode_encode_bhist witness,
        criticalStripBarrier_decode_encode_bhist real,
        criticalStripBarrier_decode_encode_bhist rational,
        criticalStripBarrier_decode_encode_bhist approach,
        criticalStripBarrier_decode_encode_bhist transport,
        criticalStripBarrier_decode_encode_bhist route,
        criticalStripBarrier_decode_encode_bhist package,
        criticalStripBarrier_decode_encode_bhist name]

private theorem criticalStripBarrierToEventFlow_injective {x y : CriticalStripBarrierUp} :
    criticalStripBarrierToEventFlow x = criticalStripBarrierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      criticalStripBarrierFromEventFlow (criticalStripBarrierToEventFlow x) =
        criticalStripBarrierFromEventFlow (criticalStripBarrierToEventFlow y) :=
    congrArg criticalStripBarrierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (criticalStripBarrier_round_trip x).symm
      (Eq.trans hread (criticalStripBarrier_round_trip y)))

private theorem CriticalStripBarrierTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CriticalStripBarrierUp,
      criticalStripBarrierFields x = criticalStripBarrierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk strip zero witness real rational approach transport route package name =>
      cases y with
      | mk strip' zero' witness' real' rational' approach' transport' route' package' name' =>
          cases hfields
          rfl

instance criticalStripBarrierBHistCarrier : BHistCarrier CriticalStripBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := criticalStripBarrierToEventFlow
  fromEventFlow := criticalStripBarrierFromEventFlow

instance criticalStripBarrierChapterTasteGate : ChapterTasteGate CriticalStripBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change criticalStripBarrierFromEventFlow (criticalStripBarrierToEventFlow x) = some x
    exact criticalStripBarrier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (criticalStripBarrierToEventFlow_injective heq)

instance criticalStripBarrierFieldFaithful : FieldFaithful CriticalStripBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := criticalStripBarrierFields
  field_faithful := CriticalStripBarrierTasteGate_single_carrier_alignment_field_faithful

theorem CriticalStripBarrierTasteGate_single_carrier_alignment :
    (∀ h : BHist, criticalStripBarrierDecodeBHist (criticalStripBarrierEncodeBHist h) = h) ∧
      (∀ x : CriticalStripBarrierUp,
        criticalStripBarrierFromEventFlow (criticalStripBarrierToEventFlow x) = some x) ∧
        (∀ x y : CriticalStripBarrierUp,
          criticalStripBarrierToEventFlow x = criticalStripBarrierToEventFlow y → x = y) ∧
          criticalStripBarrierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact criticalStripBarrier_decode_encode_bhist
  · constructor
    · exact criticalStripBarrier_round_trip
    · constructor
      · intro x y heq
        exact criticalStripBarrierToEventFlow_injective heq
      · rfl

end BEDC.Derived.CriticalStripBarrierUp

import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSealAdmissionCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSealAdmissionCutUp : Type where
  | mk :
      (request budget window readback sealRow handoff transport route provenance
        nameCert : BHist) →
      RealSealAdmissionCutUp
  deriving DecidableEq

def realSealAdmissionCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSealAdmissionCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSealAdmissionCutEncodeBHist h

def realSealAdmissionCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSealAdmissionCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSealAdmissionCutDecodeBHist tail)

private theorem realSealAdmissionCutDecode_encode_bhist :
    ∀ h : BHist, realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realSealAdmissionCutToEventFlow : RealSealAdmissionCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealAdmissionCutUp.mk request budget window readback sealRow handoff transport route
      provenance nameCert =>
      [[BMark.b0],
        realSealAdmissionCutEncodeBHist request,
        [BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realSealAdmissionCutEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realSealAdmissionCutEncodeBHist nameCert]

def realSealAdmissionCutFromEventFlow : EventFlow → Option RealSealAdmissionCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | budget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | handoff :: rest11 =>
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
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RealSealAdmissionCutUp.mk
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            request)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            budget)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            window)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            readback)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            sealRow)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            handoff)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            transport)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            route)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            provenance)
                                                                                          (realSealAdmissionCutDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

private theorem realSealAdmissionCut_round_trip :
    ∀ x : RealSealAdmissionCutUp,
      realSealAdmissionCutFromEventFlow (realSealAdmissionCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request budget window readback sealRow handoff transport route provenance nameCert =>
      change
        some
          (RealSealAdmissionCutUp.mk
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist request))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist budget))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist window))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist readback))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist sealRow))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist handoff))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist transport))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist route))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist provenance))
            (realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist nameCert))) =
          some
            (RealSealAdmissionCutUp.mk request budget window readback sealRow handoff
              transport route provenance nameCert)
      rw [realSealAdmissionCutDecode_encode_bhist request,
        realSealAdmissionCutDecode_encode_bhist budget,
        realSealAdmissionCutDecode_encode_bhist window,
        realSealAdmissionCutDecode_encode_bhist readback,
        realSealAdmissionCutDecode_encode_bhist sealRow,
        realSealAdmissionCutDecode_encode_bhist handoff,
        realSealAdmissionCutDecode_encode_bhist transport,
        realSealAdmissionCutDecode_encode_bhist route,
        realSealAdmissionCutDecode_encode_bhist provenance,
        realSealAdmissionCutDecode_encode_bhist nameCert]

private theorem realSealAdmissionCutToEventFlow_injective {x y : RealSealAdmissionCutUp} :
    realSealAdmissionCutToEventFlow x = realSealAdmissionCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSealAdmissionCutFromEventFlow (realSealAdmissionCutToEventFlow x) =
        realSealAdmissionCutFromEventFlow (realSealAdmissionCutToEventFlow y) :=
    congrArg realSealAdmissionCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSealAdmissionCut_round_trip x).symm
      (Eq.trans hread (realSealAdmissionCut_round_trip y)))

def realSealAdmissionCutFields : RealSealAdmissionCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealAdmissionCutUp.mk request budget window readback sealRow handoff transport route
      provenance nameCert =>
      [request, budget, window, readback, sealRow, handoff, transport, route, provenance,
        nameCert]

private theorem RealSealAdmissionCutTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealSealAdmissionCutUp,
      realSealAdmissionCutFields x = realSealAdmissionCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request budget window readback sealRow handoff transport route provenance nameCert =>
      cases y with
      | mk request' budget' window' readback' sealRow' handoff' transport' route' provenance'
          nameCert' =>
          cases hfields
          rfl

instance realSealAdmissionCutBHistCarrier : BHistCarrier RealSealAdmissionCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSealAdmissionCutToEventFlow
  fromEventFlow := realSealAdmissionCutFromEventFlow

instance realSealAdmissionCutChapterTasteGate : ChapterTasteGate RealSealAdmissionCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealAdmissionCutFromEventFlow (realSealAdmissionCutToEventFlow x) = some x
    exact realSealAdmissionCut_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealAdmissionCutToEventFlow_injective heq)

instance realSealAdmissionCutFieldFaithful : FieldFaithful RealSealAdmissionCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSealAdmissionCutFields
  field_faithful := RealSealAdmissionCutTasteGate_single_carrier_alignment_field_faithful

instance realSealAdmissionCutNontrivial : Nontrivial RealSealAdmissionCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSealAdmissionCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealSealAdmissionCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealSealAdmissionCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSealAdmissionCutChapterTasteGate

theorem RealSealAdmissionCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSealAdmissionCutDecodeBHist (realSealAdmissionCutEncodeBHist h) = h) ∧
      (∀ x : RealSealAdmissionCutUp,
        realSealAdmissionCutFromEventFlow (realSealAdmissionCutToEventFlow x) = some x) ∧
        (∀ x y : RealSealAdmissionCutUp,
          realSealAdmissionCutToEventFlow x = realSealAdmissionCutToEventFlow y → x = y) ∧
          realSealAdmissionCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realSealAdmissionCutDecode_encode_bhist
  · constructor
    · exact realSealAdmissionCut_round_trip
    · constructor
      · intro x y heq
        exact realSealAdmissionCutToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSealAdmissionCutUp

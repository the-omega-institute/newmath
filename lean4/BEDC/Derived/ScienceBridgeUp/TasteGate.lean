import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScienceBridgeUp.TasteGate

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScienceBridgeUp : Type where
  | mk :
      (records object audit truth bridge gaps failure transport continuation provenance
        nameCert : BHist) →
      ScienceBridgeUp
  deriving DecidableEq

def scienceBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scienceBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scienceBridgeEncodeBHist h

def scienceBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scienceBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scienceBridgeDecodeBHist tail)

theorem scienceBridgeDecodeEncodeBHist :
    ∀ h : BHist, scienceBridgeDecodeBHist (scienceBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def scienceBridgeTag0 : RawEvent := [BMark.b0]

def scienceBridgeTag1 : RawEvent := [BMark.b1, BMark.b0]

def scienceBridgeTag2 : RawEvent := [BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag3 : RawEvent := [BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag4 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag5 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag6 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag7 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag8 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
    BMark.b1, BMark.b0]

def scienceBridgeTag9 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
    BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeTag10 : RawEvent :=
  [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
    BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def scienceBridgeToEventFlow : ScienceBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ScienceBridgeUp.mk records object audit truth bridge gaps failure transport continuation
      provenance nameCert =>
      [scienceBridgeTag0, scienceBridgeEncodeBHist records,
        scienceBridgeTag1, scienceBridgeEncodeBHist object,
        scienceBridgeTag2, scienceBridgeEncodeBHist audit,
        scienceBridgeTag3, scienceBridgeEncodeBHist truth,
        scienceBridgeTag4, scienceBridgeEncodeBHist bridge,
        scienceBridgeTag5, scienceBridgeEncodeBHist gaps,
        scienceBridgeTag6, scienceBridgeEncodeBHist failure,
        scienceBridgeTag7, scienceBridgeEncodeBHist transport,
        scienceBridgeTag8, scienceBridgeEncodeBHist continuation,
        scienceBridgeTag9, scienceBridgeEncodeBHist provenance,
        scienceBridgeTag10, scienceBridgeEncodeBHist nameCert]

def scienceBridgeFromEventFlow : EventFlow → Option ScienceBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | records :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | object :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | audit :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | truth :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | bridge :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gaps :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | failure :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ScienceBridgeUp.mk
                                                                                                  (scienceBridgeDecodeBHist records)
                                                                                                  (scienceBridgeDecodeBHist object)
                                                                                                  (scienceBridgeDecodeBHist audit)
                                                                                                  (scienceBridgeDecodeBHist truth)
                                                                                                  (scienceBridgeDecodeBHist bridge)
                                                                                                  (scienceBridgeDecodeBHist gaps)
                                                                                                  (scienceBridgeDecodeBHist failure)
                                                                                                  (scienceBridgeDecodeBHist transport)
                                                                                                  (scienceBridgeDecodeBHist continuation)
                                                                                                  (scienceBridgeDecodeBHist provenance)
                                                                                                  (scienceBridgeDecodeBHist nameCert))
                                                                                          | _ :: _ => none

def scienceBridgeFields : ScienceBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScienceBridgeUp.mk records object audit truth bridge gaps failure transport continuation
      provenance nameCert =>
      [records, object, audit, truth, bridge, gaps, failure, transport, continuation,
        provenance, nameCert]

theorem scienceBridgeRoundTrip :
    ∀ x : ScienceBridgeUp, scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk records object audit truth bridge gaps failure transport continuation provenance nameCert =>
      change
        some
          (ScienceBridgeUp.mk
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist records))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist object))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist audit))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist truth))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist bridge))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist gaps))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist failure))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist transport))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist continuation))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist provenance))
            (scienceBridgeDecodeBHist (scienceBridgeEncodeBHist nameCert))) =
          some
            (ScienceBridgeUp.mk records object audit truth bridge gaps failure transport
              continuation provenance nameCert)
      rw [scienceBridgeDecodeEncodeBHist records, scienceBridgeDecodeEncodeBHist object,
        scienceBridgeDecodeEncodeBHist audit, scienceBridgeDecodeEncodeBHist truth,
        scienceBridgeDecodeEncodeBHist bridge, scienceBridgeDecodeEncodeBHist gaps,
        scienceBridgeDecodeEncodeBHist failure, scienceBridgeDecodeEncodeBHist transport,
        scienceBridgeDecodeEncodeBHist continuation, scienceBridgeDecodeEncodeBHist provenance,
        scienceBridgeDecodeEncodeBHist nameCert]

theorem scienceBridgeToEventFlow_injective {x y : ScienceBridgeUp} :
    scienceBridgeToEventFlow x = scienceBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) =
        scienceBridgeFromEventFlow (scienceBridgeToEventFlow y) :=
    congrArg scienceBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (scienceBridgeRoundTrip x).symm (Eq.trans hread (scienceBridgeRoundTrip y)))

theorem ScienceBridgeTasteGate_single_carrier_alignment_fields :
    ∀ x y : ScienceBridgeUp, scienceBridgeFields x = scienceBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk records₁ object₁ audit₁ truth₁ bridge₁ gaps₁ failure₁ transport₁ continuation₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk records₂ object₂ audit₂ truth₂ bridge₂ gaps₂ failure₂ transport₂ continuation₂
          provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance scienceBridgeBHistCarrier : BHistCarrier ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scienceBridgeToEventFlow
  fromEventFlow := scienceBridgeFromEventFlow

instance scienceBridgeChapterTasteGate : ChapterTasteGate ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scienceBridgeFromEventFlow (scienceBridgeToEventFlow x) = some x
    exact scienceBridgeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (scienceBridgeToEventFlow_injective heq)

instance scienceBridgeFieldFaithful : FieldFaithful ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := scienceBridgeFields
  field_faithful := ScienceBridgeTasteGate_single_carrier_alignment_fields

instance scienceBridgeNontrivial : Nontrivial ScienceBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ScienceBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ScienceBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ScienceBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scienceBridgeChapterTasteGate

theorem ScienceBridgeTasteGate_single_carrier_alignment :
    scienceBridgeToEventFlow
      (ScienceBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0], [], [BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          []] ∧
      Nonempty (ChapterTasteGate ScienceBridgeUp) ∧ Nonempty (FieldFaithful ScienceBridgeUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact Nonempty.intro scienceBridgeChapterTasteGate
    · exact Nonempty.intro scienceBridgeFieldFaithful

end BEDC.Derived.ScienceBridgeUp.TasteGate

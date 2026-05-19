import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZeckendorfCarryValueUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZeckendorfCarryValueUp : Type where
  | mk :
      (source target carry sourceNormal targetNormal valueRow boundary route provenance
        nameCert : BHist) →
      ZeckendorfCarryValueUp
  deriving DecidableEq

def zeckendorfCarryValueEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zeckendorfCarryValueEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zeckendorfCarryValueEncodeBHist h

def zeckendorfCarryValueDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zeckendorfCarryValueDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zeckendorfCarryValueDecodeBHist tail)

private theorem zeckendorfCarryValue_decode_encode_bhist :
    ∀ h : BHist,
      zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def zeckendorfCarryValueToEventFlow : ZeckendorfCarryValueUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
      boundary route provenance nameCert =>
      [[BMark.b0],
        zeckendorfCarryValueEncodeBHist source,
        [BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist carry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist sourceNormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist targetNormal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist valueRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        zeckendorfCarryValueEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        zeckendorfCarryValueEncodeBHist nameCert]

def zeckendorfCarryValueFromEventFlow : EventFlow → Option ZeckendorfCarryValueUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _sourceTag :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _targetTag :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _carryTag :: rest4 =>
                      match rest4 with
                      | [] => none
                      | carry :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _sourceNormalTag :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sourceNormal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _targetNormalTag :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | targetNormal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _valueTag :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | valueRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _boundaryTag :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | boundary :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _routeTag :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _provenanceTag ::
                                                                      rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _nameTag ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ZeckendorfCarryValueUp.mk
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            source)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            target)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            carry)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            sourceNormal)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            targetNormal)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            valueRow)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            boundary)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            route)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            provenance)
                                                                                          (zeckendorfCarryValueDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem zeckendorfCarryValue_round_trip :
    ∀ x : ZeckendorfCarryValueUp,
      zeckendorfCarryValueFromEventFlow (zeckendorfCarryValueToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target carry sourceNormal targetNormal valueRow boundary route provenance nameCert =>
      change
        some
          (ZeckendorfCarryValueUp.mk
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist source))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist target))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist carry))
            (zeckendorfCarryValueDecodeBHist
              (zeckendorfCarryValueEncodeBHist sourceNormal))
            (zeckendorfCarryValueDecodeBHist
              (zeckendorfCarryValueEncodeBHist targetNormal))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist valueRow))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist boundary))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist route))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist provenance))
            (zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist nameCert))) =
          some
            (ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal
              valueRow boundary route provenance nameCert)
      rw [zeckendorfCarryValue_decode_encode_bhist source,
        zeckendorfCarryValue_decode_encode_bhist target,
        zeckendorfCarryValue_decode_encode_bhist carry,
        zeckendorfCarryValue_decode_encode_bhist sourceNormal,
        zeckendorfCarryValue_decode_encode_bhist targetNormal,
        zeckendorfCarryValue_decode_encode_bhist valueRow,
        zeckendorfCarryValue_decode_encode_bhist boundary,
        zeckendorfCarryValue_decode_encode_bhist route,
        zeckendorfCarryValue_decode_encode_bhist provenance,
        zeckendorfCarryValue_decode_encode_bhist nameCert]

private theorem zeckendorfCarryValueToEventFlow_injective
    {x y : ZeckendorfCarryValueUp} :
    zeckendorfCarryValueToEventFlow x = zeckendorfCarryValueToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zeckendorfCarryValueFromEventFlow (zeckendorfCarryValueToEventFlow x) =
        zeckendorfCarryValueFromEventFlow (zeckendorfCarryValueToEventFlow y) :=
    congrArg zeckendorfCarryValueFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zeckendorfCarryValue_round_trip x).symm
      (Eq.trans hread (zeckendorfCarryValue_round_trip y)))

instance zeckendorfCarryValueBHistCarrier : BHistCarrier ZeckendorfCarryValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zeckendorfCarryValueToEventFlow
  fromEventFlow := zeckendorfCarryValueFromEventFlow

instance zeckendorfCarryValueChapterTasteGate : ChapterTasteGate ZeckendorfCarryValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zeckendorfCarryValueFromEventFlow (zeckendorfCarryValueToEventFlow x) = some x
    exact zeckendorfCarryValue_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zeckendorfCarryValueToEventFlow_injective heq)

instance zeckendorfCarryValueFieldFaithful : FieldFaithful ZeckendorfCarryValueUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ZeckendorfCarryValueUp.mk source target carry sourceNormal targetNormal valueRow
        boundary route provenance nameCert =>
        [source, target, carry, sourceNormal, targetNormal, valueRow, boundary, route,
          provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ target₁ carry₁ sourceNormal₁ targetNormal₁ valueRow₁ boundary₁ route₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk source₂ target₂ carry₂ sourceNormal₂ targetNormal₂ valueRow₂ boundary₂ route₂
            provenance₂ nameCert₂ =>
            injection h with hSource rest₁
            injection rest₁ with hTarget rest₂
            injection rest₂ with hCarry rest₃
            injection rest₃ with hSourceNormal rest₄
            injection rest₄ with hTargetNormal rest₅
            injection rest₅ with hValueRow rest₆
            injection rest₆ with hBoundary rest₇
            injection rest₇ with hRoute rest₈
            injection rest₈ with hProvenance rest₉
            injection rest₉ with hNameCert _
            cases hSource
            cases hTarget
            cases hCarry
            cases hSourceNormal
            cases hTargetNormal
            cases hValueRow
            cases hBoundary
            cases hRoute
            cases hProvenance
            cases hNameCert
            rfl

theorem ZeckendorfCarryValueTasteGate_single_carrier_alignment :
    (∀ h : BHist, zeckendorfCarryValueDecodeBHist (zeckendorfCarryValueEncodeBHist h) = h) ∧
      (∀ x : ZeckendorfCarryValueUp,
        zeckendorfCarryValueFromEventFlow (zeckendorfCarryValueToEventFlow x) = some x) ∧
        (∀ x y : ZeckendorfCarryValueUp,
          zeckendorfCarryValueToEventFlow x = zeckendorfCarryValueToEventFlow y → x = y) ∧
          zeckendorfCarryValueEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact zeckendorfCarryValue_decode_encode_bhist
  · constructor
    · exact zeckendorfCarryValue_round_trip
    · constructor
      · intro x y heq
        exact zeckendorfCarryValueToEventFlow_injective heq
      · rfl

end BEDC.Derived.ZeckendorfCarryValueUp

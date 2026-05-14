import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSealComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSealComparisonUp : Type where
  | mk :
      (seal0 seal1 uniqueness diagonal0 diagonal1 verdict transport continuation provenance
        nameCert : BHist) →
      RealSealComparisonUp
  deriving DecidableEq

def realSealComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSealComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSealComparisonEncodeBHist h

def realSealComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSealComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSealComparisonDecodeBHist tail)

private theorem realSealComparisonDecodeEncodeBHist :
    ∀ h : BHist, realSealComparisonDecodeBHist (realSealComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSealComparisonFields : RealSealComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealComparisonUp.mk seal0 seal1 uniqueness diagonal0 diagonal1 verdict transport
      continuation provenance nameCert =>
      [seal0, seal1, uniqueness, diagonal0, diagonal1, verdict, transport, continuation,
        provenance, nameCert]

def realSealComparisonToEventFlow : RealSealComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realSealComparisonFields x).map realSealComparisonEncodeBHist

def realSealComparisonFromEventFlow : EventFlow → Option RealSealComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | seal0 :: rest0 =>
      match rest0 with
      | [] => none
      | seal1 :: rest1 =>
          match rest1 with
          | [] => none
          | uniqueness :: rest2 =>
              match rest2 with
              | [] => none
              | diagonal0 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | diagonal1 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | verdict :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RealSealComparisonUp.mk
                                                  (realSealComparisonDecodeBHist seal0)
                                                  (realSealComparisonDecodeBHist seal1)
                                                  (realSealComparisonDecodeBHist uniqueness)
                                                  (realSealComparisonDecodeBHist diagonal0)
                                                  (realSealComparisonDecodeBHist diagonal1)
                                                  (realSealComparisonDecodeBHist verdict)
                                                  (realSealComparisonDecodeBHist transport)
                                                  (realSealComparisonDecodeBHist
                                                    continuation)
                                                  (realSealComparisonDecodeBHist
                                                    provenance)
                                                  (realSealComparisonDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem realSealComparison_round_trip :
    ∀ x : RealSealComparisonUp,
      realSealComparisonFromEventFlow (realSealComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk seal0 seal1 uniqueness diagonal0 diagonal1 verdict transport continuation provenance
      nameCert =>
      change
        some
          (RealSealComparisonUp.mk
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist seal0))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist seal1))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist uniqueness))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist diagonal0))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist diagonal1))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist verdict))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist transport))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist continuation))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist provenance))
            (realSealComparisonDecodeBHist (realSealComparisonEncodeBHist nameCert))) =
          some
            (RealSealComparisonUp.mk seal0 seal1 uniqueness diagonal0 diagonal1 verdict
              transport continuation provenance nameCert)
      rw [realSealComparisonDecodeEncodeBHist seal0,
        realSealComparisonDecodeEncodeBHist seal1,
        realSealComparisonDecodeEncodeBHist uniqueness,
        realSealComparisonDecodeEncodeBHist diagonal0,
        realSealComparisonDecodeEncodeBHist diagonal1,
        realSealComparisonDecodeEncodeBHist verdict,
        realSealComparisonDecodeEncodeBHist transport,
        realSealComparisonDecodeEncodeBHist continuation,
        realSealComparisonDecodeEncodeBHist provenance,
        realSealComparisonDecodeEncodeBHist nameCert]

private theorem realSealComparisonToEventFlow_injective {x y : RealSealComparisonUp} :
    realSealComparisonToEventFlow x = realSealComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk seal0₁ seal1₁ uniqueness₁ diagonal0₁ diagonal1₁ verdict₁ transport₁
      continuation₁ provenance₁ nameCert₁ =>
      cases y with
      | mk seal0₂ seal1₂ uniqueness₂ diagonal0₂ diagonal1₂ verdict₂ transport₂
          continuation₂ provenance₂ nameCert₂ =>
          intro heq
          injection heq with hseal0Raw tail0
          injection tail0 with hseal1Raw tail1
          injection tail1 with huniquenessRaw tail2
          injection tail2 with hdiagonal0Raw tail3
          injection tail3 with hdiagonal1Raw tail4
          injection tail4 with hverdictRaw tail5
          injection tail5 with htransportRaw tail6
          injection tail6 with hcontinuationRaw tail7
          injection tail7 with hprovenanceRaw tail8
          injection tail8 with hnameCertRaw _
          have hseal0 : seal0₁ = seal0₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist seal0₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hseal0Raw)
                (realSealComparisonDecodeEncodeBHist seal0₂))
          have hseal1 : seal1₁ = seal1₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist seal1₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hseal1Raw)
                (realSealComparisonDecodeEncodeBHist seal1₂))
          have huniqueness : uniqueness₁ = uniqueness₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist uniqueness₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist huniquenessRaw)
                (realSealComparisonDecodeEncodeBHist uniqueness₂))
          have hdiagonal0 : diagonal0₁ = diagonal0₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist diagonal0₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hdiagonal0Raw)
                (realSealComparisonDecodeEncodeBHist diagonal0₂))
          have hdiagonal1 : diagonal1₁ = diagonal1₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist diagonal1₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hdiagonal1Raw)
                (realSealComparisonDecodeEncodeBHist diagonal1₂))
          have hverdict : verdict₁ = verdict₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist verdict₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hverdictRaw)
                (realSealComparisonDecodeEncodeBHist verdict₂))
          have htransport : transport₁ = transport₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist transport₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist htransportRaw)
                (realSealComparisonDecodeEncodeBHist transport₂))
          have hcontinuation : continuation₁ = continuation₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist continuation₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hcontinuationRaw)
                (realSealComparisonDecodeEncodeBHist continuation₂))
          have hprovenance : provenance₁ = provenance₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist provenance₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hprovenanceRaw)
                (realSealComparisonDecodeEncodeBHist provenance₂))
          have hnameCert : nameCert₁ = nameCert₂ :=
            Eq.trans (realSealComparisonDecodeEncodeBHist nameCert₁).symm
              (Eq.trans (congrArg realSealComparisonDecodeBHist hnameCertRaw)
                (realSealComparisonDecodeEncodeBHist nameCert₂))
          cases hseal0
          cases hseal1
          cases huniqueness
          cases hdiagonal0
          cases hdiagonal1
          cases hverdict
          cases htransport
          cases hcontinuation
          cases hprovenance
          cases hnameCert
          rfl

private theorem realSealComparison_fields_faithful :
    ∀ x y : RealSealComparisonUp,
      realSealComparisonFields x = realSealComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk seal0₁ seal1₁ uniqueness₁ diagonal0₁ diagonal1₁ verdict₁ transport₁
      continuation₁ provenance₁ nameCert₁ =>
      cases y with
      | mk seal0₂ seal1₂ uniqueness₂ diagonal0₂ diagonal1₂ verdict₂ transport₂
          continuation₂ provenance₂ nameCert₂ =>
          injection hfields with hseal0 tail0
          injection tail0 with hseal1 tail1
          injection tail1 with huniqueness tail2
          injection tail2 with hdiagonal0 tail3
          injection tail3 with hdiagonal1 tail4
          injection tail4 with hverdict tail5
          injection tail5 with htransport tail6
          injection tail6 with hcontinuation tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hnameCert _
          subst hseal0
          subst hseal1
          subst huniqueness
          subst hdiagonal0
          subst hdiagonal1
          subst hverdict
          subst htransport
          subst hcontinuation
          subst hprovenance
          subst hnameCert
          rfl

instance realSealComparisonBHistCarrier : BHistCarrier RealSealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSealComparisonToEventFlow
  fromEventFlow := realSealComparisonFromEventFlow

instance realSealComparisonChapterTasteGate : ChapterTasteGate RealSealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealComparisonFromEventFlow (realSealComparisonToEventFlow x) = some x
    exact realSealComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealSealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealComparisonFromEventFlow (realSealComparisonToEventFlow x) = some x
    exact realSealComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealComparisonToEventFlow_injective heq)

instance realSealComparisonFieldFaithful : FieldFaithful RealSealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSealComparisonFields
  field_faithful := realSealComparison_fields_faithful

theorem RealSealComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSealComparisonDecodeBHist (realSealComparisonEncodeBHist h) = h) ∧
      (∀ x : RealSealComparisonUp,
        realSealComparisonFromEventFlow (realSealComparisonToEventFlow x) = some x) ∧
        (∀ x y : RealSealComparisonUp,
          realSealComparisonToEventFlow x = realSealComparisonToEventFlow y → x = y) ∧
          realSealComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realSealComparisonDecodeEncodeBHist
  · constructor
    · exact realSealComparison_round_trip
    · constructor
      · intro x y heq
        exact realSealComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSealComparisonUp

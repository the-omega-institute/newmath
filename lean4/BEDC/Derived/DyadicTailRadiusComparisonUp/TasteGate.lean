import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTailRadiusComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicTailRadiusComparisonUp : Type where
  | mk
      (ledgerLeft ledgerRight radiusLeft radiusRight comparison windowLeft windowRight
        readbackLeft readbackRight realSeal transport route provenance name : BHist) :
      DyadicTailRadiusComparisonUp
  deriving DecidableEq

def dyadicTailRadiusComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTailRadiusComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTailRadiusComparisonEncodeBHist h

def dyadicTailRadiusComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTailRadiusComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTailRadiusComparisonDecodeBHist tail)

private theorem dyadicTailRadiusComparisonDecode_encode_bhist :
    ∀ h : BHist,
      dyadicTailRadiusComparisonDecodeBHist
        (dyadicTailRadiusComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def dyadicTailRadiusComparisonDecodePacket
    (ledgerLeft ledgerRight radiusLeft radiusRight comparison windowLeft windowRight
      readbackLeft readbackRight realSeal transport route provenance name : RawEvent) :
    DyadicTailRadiusComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicTailRadiusComparisonUp.mk
    (dyadicTailRadiusComparisonDecodeBHist ledgerLeft)
    (dyadicTailRadiusComparisonDecodeBHist ledgerRight)
    (dyadicTailRadiusComparisonDecodeBHist radiusLeft)
    (dyadicTailRadiusComparisonDecodeBHist radiusRight)
    (dyadicTailRadiusComparisonDecodeBHist comparison)
    (dyadicTailRadiusComparisonDecodeBHist windowLeft)
    (dyadicTailRadiusComparisonDecodeBHist windowRight)
    (dyadicTailRadiusComparisonDecodeBHist readbackLeft)
    (dyadicTailRadiusComparisonDecodeBHist readbackRight)
    (dyadicTailRadiusComparisonDecodeBHist realSeal)
    (dyadicTailRadiusComparisonDecodeBHist transport)
    (dyadicTailRadiusComparisonDecodeBHist route)
    (dyadicTailRadiusComparisonDecodeBHist provenance)
    (dyadicTailRadiusComparisonDecodeBHist name)

def dyadicTailRadiusComparisonToEventFlow :
    DyadicTailRadiusComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailRadiusComparisonUp.mk ledgerLeft ledgerRight radiusLeft radiusRight comparison
      windowLeft windowRight readbackLeft readbackRight realSeal transport route provenance
      name =>
      [dyadicTailRadiusComparisonEncodeBHist ledgerLeft,
        dyadicTailRadiusComparisonEncodeBHist ledgerRight,
        dyadicTailRadiusComparisonEncodeBHist radiusLeft,
        dyadicTailRadiusComparisonEncodeBHist radiusRight,
        dyadicTailRadiusComparisonEncodeBHist comparison,
        dyadicTailRadiusComparisonEncodeBHist windowLeft,
        dyadicTailRadiusComparisonEncodeBHist windowRight,
        dyadicTailRadiusComparisonEncodeBHist readbackLeft,
        dyadicTailRadiusComparisonEncodeBHist readbackRight,
        dyadicTailRadiusComparisonEncodeBHist realSeal,
        dyadicTailRadiusComparisonEncodeBHist transport,
        dyadicTailRadiusComparisonEncodeBHist route,
        dyadicTailRadiusComparisonEncodeBHist provenance,
        dyadicTailRadiusComparisonEncodeBHist name]

def dyadicTailRadiusComparisonFromEventFlow :
    EventFlow → Option DyadicTailRadiusComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | ledgerLeft :: rest0 =>
      match rest0 with
      | [] => none
      | ledgerRight :: rest1 =>
          match rest1 with
          | [] => none
          | radiusLeft :: rest2 =>
              match rest2 with
              | [] => none
              | radiusRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | comparison :: rest4 =>
                      match rest4 with
                      | [] => none
                      | windowLeft :: rest5 =>
                          match rest5 with
                          | [] => none
                          | windowRight :: rest6 =>
                              match rest6 with
                              | [] => none
                              | readbackLeft :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | readbackRight :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | transport :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | provenance :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (dyadicTailRadiusComparisonDecodePacket
                                                                  ledgerLeft ledgerRight
                                                                  radiusLeft radiusRight
                                                                  comparison windowLeft
                                                                  windowRight readbackLeft
                                                                  readbackRight realSeal
                                                                  transport route provenance
                                                                  name)
                                                          | _ :: _ => none

private theorem dyadicTailRadiusComparison_round_trip :
    ∀ x : DyadicTailRadiusComparisonUp,
      dyadicTailRadiusComparisonFromEventFlow
        (dyadicTailRadiusComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ledgerLeft ledgerRight radiusLeft radiusRight comparison windowLeft windowRight
      readbackLeft readbackRight realSeal transport route provenance name =>
      change
        some
            (dyadicTailRadiusComparisonDecodePacket
              (dyadicTailRadiusComparisonEncodeBHist ledgerLeft)
              (dyadicTailRadiusComparisonEncodeBHist ledgerRight)
              (dyadicTailRadiusComparisonEncodeBHist radiusLeft)
              (dyadicTailRadiusComparisonEncodeBHist radiusRight)
              (dyadicTailRadiusComparisonEncodeBHist comparison)
              (dyadicTailRadiusComparisonEncodeBHist windowLeft)
              (dyadicTailRadiusComparisonEncodeBHist windowRight)
              (dyadicTailRadiusComparisonEncodeBHist readbackLeft)
              (dyadicTailRadiusComparisonEncodeBHist readbackRight)
              (dyadicTailRadiusComparisonEncodeBHist realSeal)
              (dyadicTailRadiusComparisonEncodeBHist transport)
              (dyadicTailRadiusComparisonEncodeBHist route)
              (dyadicTailRadiusComparisonEncodeBHist provenance)
              (dyadicTailRadiusComparisonEncodeBHist name)) =
          some
            (DyadicTailRadiusComparisonUp.mk ledgerLeft ledgerRight radiusLeft radiusRight
              comparison windowLeft windowRight readbackLeft readbackRight realSeal
              transport route provenance name)
      unfold dyadicTailRadiusComparisonDecodePacket
      rw [dyadicTailRadiusComparisonDecode_encode_bhist ledgerLeft,
        dyadicTailRadiusComparisonDecode_encode_bhist ledgerRight,
        dyadicTailRadiusComparisonDecode_encode_bhist radiusLeft,
        dyadicTailRadiusComparisonDecode_encode_bhist radiusRight,
        dyadicTailRadiusComparisonDecode_encode_bhist comparison,
        dyadicTailRadiusComparisonDecode_encode_bhist windowLeft,
        dyadicTailRadiusComparisonDecode_encode_bhist windowRight,
        dyadicTailRadiusComparisonDecode_encode_bhist readbackLeft,
        dyadicTailRadiusComparisonDecode_encode_bhist readbackRight,
        dyadicTailRadiusComparisonDecode_encode_bhist realSeal,
        dyadicTailRadiusComparisonDecode_encode_bhist transport,
        dyadicTailRadiusComparisonDecode_encode_bhist route,
        dyadicTailRadiusComparisonDecode_encode_bhist provenance,
        dyadicTailRadiusComparisonDecode_encode_bhist name]

private theorem dyadicTailRadiusComparisonToEventFlow_injective
    {x y : DyadicTailRadiusComparisonUp} :
    dyadicTailRadiusComparisonToEventFlow x =
      dyadicTailRadiusComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTailRadiusComparisonFromEventFlow
          (dyadicTailRadiusComparisonToEventFlow x) =
        dyadicTailRadiusComparisonFromEventFlow
          (dyadicTailRadiusComparisonToEventFlow y) :=
    congrArg dyadicTailRadiusComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicTailRadiusComparison_round_trip x).symm
      (Eq.trans hread (dyadicTailRadiusComparison_round_trip y)))

def dyadicTailRadiusComparisonFields :
    DyadicTailRadiusComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailRadiusComparisonUp.mk ledgerLeft ledgerRight radiusLeft radiusRight comparison
      windowLeft windowRight readbackLeft readbackRight realSeal transport route provenance
      name =>
      [ledgerLeft, ledgerRight, radiusLeft, radiusRight, comparison, windowLeft, windowRight,
        readbackLeft, readbackRight, realSeal, transport, route, provenance, name]

private theorem dyadicTailRadiusComparison_fields_faithful :
    ∀ x y : DyadicTailRadiusComparisonUp,
      dyadicTailRadiusComparisonFields x =
        dyadicTailRadiusComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  exact dyadicTailRadiusComparisonToEventFlow_injective (by
    cases x with
    | mk ledgerLeft₁ ledgerRight₁ radiusLeft₁ radiusRight₁ comparison₁ windowLeft₁
        windowRight₁ readbackLeft₁ readbackRight₁ realSeal₁ transport₁ route₁ provenance₁
        name₁ =>
        cases y with
        | mk ledgerLeft₂ ledgerRight₂ radiusLeft₂ radiusRight₂ comparison₂ windowLeft₂
            windowRight₂ readbackLeft₂ readbackRight₂ realSeal₂ transport₂ route₂ provenance₂
            name₂ =>
            injection hfields with hLedgerLeft tail0
            injection tail0 with hLedgerRight tail1
            injection tail1 with hRadiusLeft tail2
            injection tail2 with hRadiusRight tail3
            injection tail3 with hComparison tail4
            injection tail4 with hWindowLeft tail5
            injection tail5 with hWindowRight tail6
            injection tail6 with hReadbackLeft tail7
            injection tail7 with hReadbackRight tail8
            injection tail8 with hRealSeal tail9
            injection tail9 with hTransport tail10
            injection tail10 with hRoute tail11
            injection tail11 with hProvenance tail12
            injection tail12 with hName _
            subst hLedgerLeft
            subst hLedgerRight
            subst hRadiusLeft
            subst hRadiusRight
            subst hComparison
            subst hWindowLeft
            subst hWindowRight
            subst hReadbackLeft
            subst hReadbackRight
            subst hRealSeal
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl)

instance dyadicTailRadiusComparisonBHistCarrier :
    BHistCarrier DyadicTailRadiusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicTailRadiusComparisonToEventFlow
  fromEventFlow := dyadicTailRadiusComparisonFromEventFlow

instance dyadicTailRadiusComparisonChapterTasteGate :
    ChapterTasteGate DyadicTailRadiusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicTailRadiusComparisonFromEventFlow
        (dyadicTailRadiusComparisonToEventFlow x) = some x
    exact dyadicTailRadiusComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicTailRadiusComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicTailRadiusComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicTailRadiusComparisonChapterTasteGate

instance dyadicTailRadiusComparisonFieldFaithful :
    FieldFaithful DyadicTailRadiusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicTailRadiusComparisonFields
  field_faithful := dyadicTailRadiusComparison_fields_faithful

instance dyadicTailRadiusComparisonNontrivial :
    Nontrivial DyadicTailRadiusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicTailRadiusComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicTailRadiusComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DyadicTailRadiusComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicTailRadiusComparisonDecodeBHist
        (dyadicTailRadiusComparisonEncodeBHist h) = h) ∧
      (∀ x : DyadicTailRadiusComparisonUp,
        dyadicTailRadiusComparisonFromEventFlow
          (dyadicTailRadiusComparisonToEventFlow x) = some x) ∧
        (∀ x y : DyadicTailRadiusComparisonUp,
          dyadicTailRadiusComparisonToEventFlow x =
            dyadicTailRadiusComparisonToEventFlow y → x = y) ∧
          dyadicTailRadiusComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicTailRadiusComparisonDecode_encode_bhist
  · constructor
    · intro x
      change
        dyadicTailRadiusComparisonFromEventFlow
          (dyadicTailRadiusComparisonToEventFlow x) = some x
      exact dyadicTailRadiusComparison_round_trip x
    · constructor
      · intro x y heq
        exact dyadicTailRadiusComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicTailRadiusComparisonUp

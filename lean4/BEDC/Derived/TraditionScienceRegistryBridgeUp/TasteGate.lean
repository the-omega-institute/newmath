import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraditionScienceRegistryBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraditionScienceRegistryBridgeUp : Type where
  | mk :
      (traditionEntry preservedStructure rejectedSurplus scienceEntry empiricalLedger
        failureSurface componentHsame continuation provenance localName : BHist) →
      TraditionScienceRegistryBridgeUp
  deriving DecidableEq

def traditionScienceRegistryBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traditionScienceRegistryBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traditionScienceRegistryBridgeEncodeBHist h

def traditionScienceRegistryBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traditionScienceRegistryBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traditionScienceRegistryBridgeDecodeBHist tail)

private theorem traditionScienceRegistryBridgeDecodeEncodeBHist :
    ∀ h : BHist,
      traditionScienceRegistryBridgeDecodeBHist
        (traditionScienceRegistryBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def traditionScienceRegistryBridgeFields :
    TraditionScienceRegistryBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionScienceRegistryBridgeUp.mk traditionEntry preservedStructure rejectedSurplus
      scienceEntry empiricalLedger failureSurface componentHsame continuation provenance
      localName =>
      [traditionEntry, preservedStructure, rejectedSurplus, scienceEntry, empiricalLedger,
        failureSurface, componentHsame, continuation, provenance, localName]

def traditionScienceRegistryBridgeToEventFlow :
    TraditionScienceRegistryBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionScienceRegistryBridgeUp.mk traditionEntry preservedStructure rejectedSurplus
      scienceEntry empiricalLedger failureSurface componentHsame continuation provenance
      localName =>
      [traditionScienceRegistryBridgeEncodeBHist traditionEntry,
        traditionScienceRegistryBridgeEncodeBHist preservedStructure,
        traditionScienceRegistryBridgeEncodeBHist rejectedSurplus,
        traditionScienceRegistryBridgeEncodeBHist scienceEntry,
        traditionScienceRegistryBridgeEncodeBHist empiricalLedger,
        traditionScienceRegistryBridgeEncodeBHist failureSurface,
        traditionScienceRegistryBridgeEncodeBHist componentHsame,
        traditionScienceRegistryBridgeEncodeBHist continuation,
        traditionScienceRegistryBridgeEncodeBHist provenance,
        traditionScienceRegistryBridgeEncodeBHist localName]

def traditionScienceRegistryBridgeFromEventFlow :
    EventFlow → Option TraditionScienceRegistryBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | traditionEntry :: rest0 =>
      match rest0 with
      | [] => none
      | preservedStructure :: rest1 =>
          match rest1 with
          | [] => none
          | rejectedSurplus :: rest2 =>
              match rest2 with
              | [] => none
              | scienceEntry :: rest3 =>
                  match rest3 with
                  | [] => none
                  | empiricalLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | failureSurface :: rest5 =>
                          match rest5 with
                          | [] => none
                          | componentHsame :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (TraditionScienceRegistryBridgeUp.mk
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    traditionEntry)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    preservedStructure)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    rejectedSurplus)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    scienceEntry)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    empiricalLedger)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    failureSurface)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    componentHsame)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    continuation)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    provenance)
                                                  (traditionScienceRegistryBridgeDecodeBHist
                                                    localName))
                                          | _ :: _ => none

private theorem traditionScienceRegistryBridge_round_trip :
    ∀ x : TraditionScienceRegistryBridgeUp,
      traditionScienceRegistryBridgeFromEventFlow
          (traditionScienceRegistryBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk traditionEntry preservedStructure rejectedSurplus scienceEntry empiricalLedger
      failureSurface componentHsame continuation provenance localName =>
      change
        some
          (TraditionScienceRegistryBridgeUp.mk
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist traditionEntry))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist preservedStructure))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist rejectedSurplus))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist scienceEntry))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist empiricalLedger))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist failureSurface))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist componentHsame))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist continuation))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist provenance))
            (traditionScienceRegistryBridgeDecodeBHist
              (traditionScienceRegistryBridgeEncodeBHist localName))) =
          some
            (TraditionScienceRegistryBridgeUp.mk traditionEntry preservedStructure
              rejectedSurplus scienceEntry empiricalLedger failureSurface componentHsame
              continuation provenance localName)
      rw [traditionScienceRegistryBridgeDecodeEncodeBHist traditionEntry,
        traditionScienceRegistryBridgeDecodeEncodeBHist preservedStructure,
        traditionScienceRegistryBridgeDecodeEncodeBHist rejectedSurplus,
        traditionScienceRegistryBridgeDecodeEncodeBHist scienceEntry,
        traditionScienceRegistryBridgeDecodeEncodeBHist empiricalLedger,
        traditionScienceRegistryBridgeDecodeEncodeBHist failureSurface,
        traditionScienceRegistryBridgeDecodeEncodeBHist componentHsame,
        traditionScienceRegistryBridgeDecodeEncodeBHist continuation,
        traditionScienceRegistryBridgeDecodeEncodeBHist provenance,
        traditionScienceRegistryBridgeDecodeEncodeBHist localName]

private theorem traditionScienceRegistryBridgeToEventFlow_injective
    {x y : TraditionScienceRegistryBridgeUp} :
    traditionScienceRegistryBridgeToEventFlow x =
      traditionScienceRegistryBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traditionScienceRegistryBridgeFromEventFlow
          (traditionScienceRegistryBridgeToEventFlow x) =
        traditionScienceRegistryBridgeFromEventFlow
          (traditionScienceRegistryBridgeToEventFlow y) :=
    congrArg traditionScienceRegistryBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (traditionScienceRegistryBridge_round_trip x).symm
      (Eq.trans hread (traditionScienceRegistryBridge_round_trip y)))

private theorem traditionScienceRegistryBridge_field_faithful :
    ∀ x y : TraditionScienceRegistryBridgeUp,
      traditionScienceRegistryBridgeFields x = traditionScienceRegistryBridgeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk traditionEntry₁ preservedStructure₁ rejectedSurplus₁ scienceEntry₁ empiricalLedger₁
      failureSurface₁ componentHsame₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk traditionEntry₂ preservedStructure₂ rejectedSurplus₂ scienceEntry₂ empiricalLedger₂
          failureSurface₂ componentHsame₂ continuation₂ provenance₂ localName₂ =>
          injection hfields with htraditionEntry tail0
          injection tail0 with hpreservedStructure tail1
          injection tail1 with hrejectedSurplus tail2
          injection tail2 with hscienceEntry tail3
          injection tail3 with hempiricalLedger tail4
          injection tail4 with hfailureSurface tail5
          injection tail5 with hcomponentHsame tail6
          injection tail6 with hcontinuation tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hlocalName _
          subst htraditionEntry
          subst hpreservedStructure
          subst hrejectedSurplus
          subst hscienceEntry
          subst hempiricalLedger
          subst hfailureSurface
          subst hcomponentHsame
          subst hcontinuation
          subst hprovenance
          subst hlocalName
          rfl

instance traditionScienceRegistryBridgeBHistCarrier :
    BHistCarrier TraditionScienceRegistryBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traditionScienceRegistryBridgeToEventFlow
  fromEventFlow := traditionScienceRegistryBridgeFromEventFlow

instance traditionScienceRegistryBridgeChapterTasteGate :
    ChapterTasteGate TraditionScienceRegistryBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change traditionScienceRegistryBridgeFromEventFlow
        (traditionScienceRegistryBridgeToEventFlow x) =
      some x
    exact traditionScienceRegistryBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (traditionScienceRegistryBridgeToEventFlow_injective heq)

instance traditionScienceRegistryBridgeFieldFaithful :
    FieldFaithful TraditionScienceRegistryBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traditionScienceRegistryBridgeFields
  field_faithful := traditionScienceRegistryBridge_field_faithful

instance traditionScienceRegistryBridgeNontrivial :
    Nontrivial TraditionScienceRegistryBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraditionScienceRegistryBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      TraditionScienceRegistryBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TraditionScienceRegistryBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  traditionScienceRegistryBridgeChapterTasteGate

theorem TraditionScienceRegistryBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, traditionScienceRegistryBridgeDecodeBHist
      (traditionScienceRegistryBridgeEncodeBHist h) = h) ∧
      (∀ x : TraditionScienceRegistryBridgeUp,
        traditionScienceRegistryBridgeFromEventFlow
            (traditionScienceRegistryBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : TraditionScienceRegistryBridgeUp,
          traditionScienceRegistryBridgeToEventFlow x =
            traditionScienceRegistryBridgeToEventFlow y →
              x = y) ∧
          traditionScienceRegistryBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact traditionScienceRegistryBridgeDecodeEncodeBHist
  · constructor
    · exact traditionScienceRegistryBridge_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk traditionEntry₁ preservedStructure₁ rejectedSurplus₁ scienceEntry₁
            empiricalLedger₁ failureSurface₁ componentHsame₁ continuation₁ provenance₁
            localName₁ =>
            cases y with
            | mk traditionEntry₂ preservedStructure₂ rejectedSurplus₂ scienceEntry₂
                empiricalLedger₂ failureSurface₂ componentHsame₂ continuation₂ provenance₂
                localName₂ =>
                injection heq with htraditionEntry tail0
                injection tail0 with hpreservedStructure tail1
                injection tail1 with hrejectedSurplus tail2
                injection tail2 with hscienceEntry tail3
                injection tail3 with hempiricalLedger tail4
                injection tail4 with hfailureSurface tail5
                injection tail5 with hcomponentHsame tail6
                injection tail6 with hcontinuation tail7
                injection tail7 with hprovenance tail8
                injection tail8 with hlocalName _
                have traditionEntryEq : traditionEntry₁ = traditionEntry₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist htraditionEntry
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist traditionEntry₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist traditionEntry₂] at hdecode
                  exact hdecode
                have preservedStructureEq : preservedStructure₁ = preservedStructure₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hpreservedStructure
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist preservedStructure₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist preservedStructure₂] at hdecode
                  exact hdecode
                have rejectedSurplusEq : rejectedSurplus₁ = rejectedSurplus₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hrejectedSurplus
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist rejectedSurplus₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist rejectedSurplus₂] at hdecode
                  exact hdecode
                have scienceEntryEq : scienceEntry₁ = scienceEntry₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hscienceEntry
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist scienceEntry₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist scienceEntry₂] at hdecode
                  exact hdecode
                have empiricalLedgerEq : empiricalLedger₁ = empiricalLedger₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hempiricalLedger
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist empiricalLedger₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist empiricalLedger₂] at hdecode
                  exact hdecode
                have failureSurfaceEq : failureSurface₁ = failureSurface₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hfailureSurface
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist failureSurface₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist failureSurface₂] at hdecode
                  exact hdecode
                have componentHsameEq : componentHsame₁ = componentHsame₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hcomponentHsame
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist componentHsame₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist componentHsame₂] at hdecode
                  exact hdecode
                have continuationEq : continuation₁ = continuation₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hcontinuation
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist continuation₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist continuation₂] at hdecode
                  exact hdecode
                have provenanceEq : provenance₁ = provenance₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hprovenance
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist provenance₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist provenance₂] at hdecode
                  exact hdecode
                have localNameEq : localName₁ = localName₂ := by
                  have hdecode :=
                    congrArg traditionScienceRegistryBridgeDecodeBHist hlocalName
                  rw [traditionScienceRegistryBridgeDecodeEncodeBHist localName₁,
                    traditionScienceRegistryBridgeDecodeEncodeBHist localName₂] at hdecode
                  exact hdecode
                cases traditionEntryEq
                cases preservedStructureEq
                cases rejectedSurplusEq
                cases scienceEntryEq
                cases empiricalLedgerEq
                cases failureSurfaceEq
                cases componentHsameEq
                cases continuationEq
                cases provenanceEq
                cases localNameEq
                rfl
      · rfl

end BEDC.Derived.TraditionScienceRegistryBridgeUp

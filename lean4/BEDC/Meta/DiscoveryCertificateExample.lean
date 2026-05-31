import BEDC.Meta.DiscoveryCertificate

namespace BEDC.Meta.DiscoveryCertificateExample

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.DiscoveryCertificate

def SmokeScope (_h : BHist) : Prop := True

def SmokeSource (_h : BHist) : Prop := True

def SmokeClassifierBefore (h k : BHist) : Prop := hsame h k

def SmokeClassifierAfter (_h _k : BHist) : Prop := True

def smokeBeforeNameCert : NameCert SmokeSource SmokeClassifierBefore where
  carrier_inhabited := Exists.intro BHist.Empty True.intro
  equiv_refl := by
    intro h _source
    exact hsame_refl h
  equiv_symm := by
    intro h k same
    exact hsame_symm same
  equiv_trans := by
    intro a b c sameAB sameBC
    exact hsame_trans sameAB sameBC
  carrier_respects_equiv := by
    intro h k _same _source
    exact True.intro

def smokeAfterNameCert : NameCert SmokeSource SmokeClassifierAfter where
  carrier_inhabited := Exists.intro BHist.Empty True.intro
  equiv_refl := by
    intro h _source
    exact True.intro
  equiv_symm := by
    intro h k _same
    exact True.intro
  equiv_trans := by
    intro a b c _sameAB _sameBC
    exact True.intro
  carrier_respects_equiv := by
    intro h k _same _source
    exact True.intro

def smokeBeforeSemantic :
    SemanticNameCert
      SmokeSource SmokeSource SmokeSource SmokeClassifierBefore :=
  NameCert_carrier_self_semantic_lifting smokeBeforeNameCert

def smokeAfterSemantic :
    SemanticNameCert
      SmokeSource SmokeSource SmokeSource SmokeClassifierAfter :=
  NameCert_carrier_self_semantic_lifting smokeAfterNameCert

def smokeBeforeState :
    CertifiedClassifierState
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierBefore where
  semantic_namecert := smokeBeforeSemantic
  stability_sound := by
    intro h source
    exact source

def smokeAfterState :
    CertifiedClassifierState
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierAfter where
  semantic_namecert := smokeAfterSemantic
  stability_sound := by
    intro h source
    exact source

def smokeBeforeRows : NameCertFiveRows smokeBeforeState where
  source := ⟨BHist.Empty, True.intro⟩
  pattern := ⟨BHist.Empty, And.intro True.intro True.intro⟩
  classifier := ⟨BHist.Empty, And.intro True.intro (hsame_refl BHist.Empty)⟩
  stability := ⟨BHist.Empty, And.intro True.intro True.intro⟩
  ledger := ⟨BHist.Empty, And.intro True.intro True.intro⟩

def smokeAfterRows : NameCertFiveRows smokeAfterState where
  source := ⟨BHist.Empty, True.intro⟩
  pattern := ⟨BHist.Empty, And.intro True.intro True.intro⟩
  classifier := ⟨BHist.Empty, And.intro True.intro True.intro⟩
  stability := ⟨BHist.Empty, And.intro True.intro True.intro⟩
  ledger := ⟨BHist.Empty, And.intro True.intro True.intro⟩

def smokeDisagreement :
    ClassifierDisagreement
      SmokeScope SmokeSource SmokeSource
      SmokeClassifierAfter SmokeClassifierBefore where
  left := BHist.Empty
  right := BHist.e0 BHist.Empty
  left_scope := True.intro
  right_scope := True.intro
  left_source_a := True.intro
  right_source_a := True.intro
  left_source_b := True.intro
  right_source_b := True.intro
  positive := True.intro
  negative := by
    intro same
    exact not_hsame_emp_e0 same

def smokeStructuralDiscovery :
    StructuralDiscovery
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierBefore
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierAfter where
  before_state := smokeBeforeState
  after_state := smokeAfterState
  before_rows := smokeBeforeRows
  after_rows := smokeAfterRows
  scope := SmokeScope
  classifier_shift := ClassifierNonEquivalent.right smokeDisagreement

def smokeDiscoveryCost : DiscoveryCost where
  benefit := 1
  cost := 0
  debt := 0
  scopeSeal := 0
  positive_margin := Nat.zero_lt_succ 0

def smokeScopeSeal : ScopeSeal where
  carrier := SmokeScope
  anchor := BHist.Empty
  anchored := True.intro

def smokePositiveDiscovery :
    PositiveDiscovery
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierBefore
      SmokeSource SmokeSource SmokeSource SmokeSource SmokeClassifierAfter where
  benefit := smokeStructuralDiscovery
  cost := smokeDiscoveryCost
  debt := BHist.Empty
  scope_seal := smokeScopeSeal
  debt_in_after_ledger := True.intro
  scope_seal_in_discovery_scope := True.intro

theorem smokeRefutesClassifierEquivalentOn :
    Not
      (ClassifierEquivalentOn
        SmokeScope SmokeSource SmokeSource
        SmokeClassifierBefore SmokeClassifierAfter) := by
  exact
    classifierNonEquivalent_not_equivalentOn
      smokeStructuralDiscovery.classifier_shift

theorem smokePositiveCostProtocol :
    PositiveCostProtocol
      smokePositiveDiscovery.cost.benefit
      smokePositiveDiscovery.cost.cost
      smokePositiveDiscovery.cost.debt
      smokePositiveDiscovery.cost.scopeSeal := by
  exact positiveDiscovery_positive_cost smokePositiveDiscovery

end BEDC.Meta.DiscoveryCertificateExample

import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Meta.DiscoveryCertificate

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

structure CertifiedClassifierState
    (SourceSpec PatternSpec LedgerPolicy : BHist -> Prop)
    (ClassifierSpec : BHist -> BHist -> Prop) where
  semantic_namecert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec

structure NameCertFiveRows
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state : CertifiedClassifierState SourceSpec PatternSpec LedgerPolicy ClassifierSpec) where
  source : BHist
  pattern : BHist
  classifier : BHist
  stability : BHist
  ledger : BHist
  source_member : SourceSpec source
  pattern_member : SourceSpec pattern
  classifier_member : SourceSpec classifier
  stability_member : SourceSpec stability
  ledger_member : SourceSpec ledger

def ClassifierEquivalentOn
    (Scope : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) : Prop :=
  forall {h k : BHist}, Scope h -> Scope k ->
    (ClassifierA h k -> ClassifierB h k) ∧
      (ClassifierB h k -> ClassifierA h k)

structure ClassifierDisagreement
    (Scope : BHist -> Prop)
    (SourceA SourceB : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) where
  (left right : BHist)
  (left_scope : Scope left)
  (right_scope : Scope right)
  (left_source_a : SourceA left)
  (right_source_a : SourceA right)
  (left_source_b : SourceB left)
  (right_source_b : SourceB right)
  (positive : ClassifierA left right)
  (negative : ClassifierB left right -> False)

inductive ClassifierNonEquivalent
    (Scope : BHist -> Prop)
    (SourceA SourceB : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) : Prop where
  | left :
      ClassifierDisagreement Scope SourceA SourceB ClassifierA ClassifierB ->
      ClassifierNonEquivalent Scope SourceA SourceB ClassifierA ClassifierB
  | right :
      ClassifierDisagreement Scope SourceB SourceA ClassifierB ClassifierA ->
      ClassifierNonEquivalent Scope SourceA SourceB ClassifierA ClassifierB

structure ScopeSeal where
  carrier : BHist -> Prop
  anchor : BHist
  anchored : carrier anchor

structure DiscoveryCost where
  benefit : Nat
  cost : Nat
  debt : Nat
  scopeSeal : Nat
  positive_margin : cost + debt + scopeSeal < benefit

theorem costPositive (cost : DiscoveryCost) :
    cost.cost + cost.debt + cost.scopeSeal < cost.benefit := by
  exact cost.positive_margin

theorem discoveryCost_benefit_positive (cost : DiscoveryCost) : cost.benefit > 0 := by
  cases cost with
  | mk benefit cost debt scopeSeal positive_margin =>
  cases benefit with
  | zero =>
      have impossible : cost + debt + scopeSeal < 0 := positive_margin
      cases impossible
  | succ n =>
      exact Nat.zero_lt_succ n

structure StructuralDiscovery
    (BeforeSource BeforePattern BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  before_state :
    CertifiedClassifierState BeforeSource BeforePattern BeforeLedger BeforeClassifier
  after_state :
    CertifiedClassifierState AfterSource AfterPattern AfterLedger AfterClassifier
  before_rows : NameCertFiveRows before_state
  after_rows : NameCertFiveRows after_state
  scope : BHist -> Prop
  classifier_shift :
    ClassifierNonEquivalent scope BeforeSource AfterSource BeforeClassifier AfterClassifier

structure PositiveDiscovery
    (BeforeSource BeforePattern BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  benefit :
    StructuralDiscovery
      BeforeSource BeforePattern BeforeLedger BeforeClassifier
      AfterSource AfterPattern AfterLedger AfterClassifier
  cost : DiscoveryCost
  debt : BHist
  scope_seal : ScopeSeal
  debt_in_after_ledger : AfterLedger debt
  scope_seal_in_discovery_scope : benefit.scope scope_seal.anchor

structure DiscoveryTasteGate
    (X : Type)
    [BHistCarrier X]
    (BeforeSource BeforePattern BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  positive :
    PositiveDiscovery
      BeforeSource BeforePattern BeforeLedger BeforeClassifier
      AfterSource AfterPattern AfterLedger AfterClassifier
  admission : ChapterTasteGate X

theorem certifiedClassifierState_semantic_namecert
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state : CertifiedClassifierState SourceSpec PatternSpec LedgerPolicy ClassifierSpec) :
    SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec := by
  exact state.semantic_namecert

theorem certifiedClassifierState_ledger_witness
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state : CertifiedClassifierState SourceSpec PatternSpec LedgerPolicy ClassifierSpec) :
    exists h : BHist, LedgerPolicy h := by
  exact semanticNameCert_ledger_policy_witness state.semantic_namecert

theorem structuralDiscovery_classifier_shift
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    ClassifierNonEquivalent discovery.scope BeforeSource AfterSource
      BeforeClassifier AfterClassifier := by
  exact discovery.classifier_shift

theorem structuralDiscovery_after_rows
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    exists rows : NameCertFiveRows discovery.after_state, rows = discovery.after_rows := by
  exact Exists.intro discovery.after_rows rfl

theorem nameCertFiveRows_classifier_self
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    {state : CertifiedClassifierState SourceSpec PatternSpec LedgerPolicy ClassifierSpec}
    (rows : NameCertFiveRows state) :
    ClassifierSpec rows.classifier rows.classifier := by
  exact state.semantic_namecert.core.equiv_refl rows.classifier_member

theorem nameCertFiveRows_pattern_ledger
    {SourceSpec PatternSpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    {state : CertifiedClassifierState SourceSpec PatternSpec LedgerPolicy ClassifierSpec}
    (rows : NameCertFiveRows state) :
    PatternSpec rows.source ∧ LedgerPolicy rows.source := by
  exact And.intro
    (state.semantic_namecert.pattern_sound rows.source_member)
    (state.semantic_namecert.ledger_sound rows.source_member)

theorem positiveDiscovery_structural
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    exists structural :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier,
      structural = discovery.benefit := by
  exact Exists.intro discovery.benefit rfl

theorem positiveDiscovery_positive_cost
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    discovery.cost.benefit > 0 := by
  exact discoveryCost_benefit_positive discovery.cost

theorem positiveDiscovery_classifier_shift
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    ClassifierNonEquivalent discovery.benefit.scope BeforeSource AfterSource
      BeforeClassifier AfterClassifier := by
  exact structuralDiscovery_classifier_shift discovery.benefit

theorem discoveryTasteGate_positive
    {X : Type}
    [BHistCarrier X]
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (gate :
      DiscoveryTasteGate X
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    exists positive :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier,
      positive = gate.positive := by
  exact Exists.intro gate.positive rfl

end BEDC.Meta.DiscoveryCertificate

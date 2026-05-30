import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Meta.DiscoveryCertificate

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

structure CertifiedClassifierState
    (SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop)
    (ClassifierSpec : BHist -> BHist -> Prop) where
  semantic_namecert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec
  stability_sound : forall {h : BHist}, SourceSpec h -> StabilitySpec h

structure NameCertFiveRows
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state : CertifiedClassifierState
      SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec) where
  source : {h : BHist // SourceSpec h}
  pattern : {h : BHist // SourceSpec h ∧ PatternSpec h}
  classifier : {h : BHist // SourceSpec h ∧ ClassifierSpec h h}
  stability : {h : BHist // SourceSpec h ∧ StabilitySpec h}
  ledger : {h : BHist // SourceSpec h ∧ LedgerPolicy h}

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
    (BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  before_state :
    CertifiedClassifierState
      BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
  after_state :
    CertifiedClassifierState
      AfterSource AfterPattern AfterStability AfterLedger AfterClassifier
  before_rows : NameCertFiveRows before_state
  after_rows : NameCertFiveRows after_state
  scope : BHist -> Prop
  classifier_shift :
    ClassifierNonEquivalent scope BeforeSource AfterSource BeforeClassifier AfterClassifier

structure PositiveDiscovery
    (BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  benefit :
    StructuralDiscovery
      BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
      AfterSource AfterPattern AfterStability AfterLedger AfterClassifier
  cost : DiscoveryCost
  debt : BHist
  scope_seal : ScopeSeal
  debt_in_after_ledger : AfterLedger debt
  scope_seal_in_discovery_scope : benefit.scope scope_seal.anchor

structure DiscoveryTasteGate
    (X : Type)
    [BHistCarrier X]
    (BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  positive :
    PositiveDiscovery
      BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
      AfterSource AfterPattern AfterStability AfterLedger AfterClassifier
  admission : ChapterTasteGate X

theorem certifiedClassifierState_semantic_namecert
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec) :
    SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec := by
  exact state.semantic_namecert

theorem certifiedClassifierState_stability_sound
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec)
    {h : BHist} :
    SourceSpec h -> StabilitySpec h := by
  exact state.stability_sound

theorem certifiedClassifierState_ledger_witness
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    (state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec) :
    exists h : BHist, LedgerPolicy h := by
  exact semanticNameCert_ledger_policy_witness state.semantic_namecert

theorem structuralDiscovery_classifier_shift
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    ClassifierNonEquivalent discovery.scope BeforeSource AfterSource
      BeforeClassifier AfterClassifier := by
  exact discovery.classifier_shift

theorem structuralDiscovery_after_rows
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    exists rows : NameCertFiveRows discovery.after_state, rows = discovery.after_rows := by
  exact Exists.intro discovery.after_rows rfl

theorem nameCertFiveRows_classifier_self
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    {state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec}
    (rows : NameCertFiveRows state) :
    ClassifierSpec rows.classifier.val rows.classifier.val := by
  exact rows.classifier.property.right

theorem nameCertFiveRows_pattern_ledger
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    {state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec}
    (rows : NameCertFiveRows state) :
    PatternSpec rows.pattern.val ∧ LedgerPolicy rows.ledger.val := by
  exact And.intro
    rows.pattern.property.right
    rows.ledger.property.right

theorem nameCertFiveRows_named_row_projection
    {SourceSpec PatternSpec StabilitySpec LedgerPolicy : BHist -> Prop}
    {ClassifierSpec : BHist -> BHist -> Prop}
    {state :
      CertifiedClassifierState
        SourceSpec PatternSpec StabilitySpec LedgerPolicy ClassifierSpec}
    (rows : NameCertFiveRows state) :
    PatternSpec rows.pattern.val ∧
      StabilitySpec rows.stability.val ∧
        LedgerPolicy rows.ledger.val := by
  exact And.intro
    (state.semantic_namecert.pattern_sound rows.pattern.property.left)
    (And.intro
      (state.stability_sound rows.stability.property.left)
      (state.semantic_namecert.ledger_sound rows.ledger.property.left))

theorem positiveDiscovery_structural
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    exists structural :
      StructuralDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier,
      structural = discovery.benefit := by
  exact Exists.intro discovery.benefit rfl

theorem positiveDiscovery_positive_cost
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    discovery.cost.cost + discovery.cost.debt + discovery.cost.scopeSeal <
      discovery.cost.benefit := by
  exact costPositive discovery.cost

theorem positiveDiscovery_classifier_shift
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    ClassifierNonEquivalent discovery.benefit.scope BeforeSource AfterSource
      BeforeClassifier AfterClassifier := by
  exact structuralDiscovery_classifier_shift discovery.benefit

theorem discoveryTasteGate_positive
    {X : Type}
    [BHistCarrier X]
    {BeforeSource BeforePattern BeforeStability BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterStability AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (gate :
      DiscoveryTasteGate X
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier) :
    exists positive :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeStability BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterStability AfterLedger AfterClassifier,
      positive = gate.positive := by
  exact Exists.intro gate.positive rfl

end BEDC.Meta.DiscoveryCertificate

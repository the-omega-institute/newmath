import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Meta.DiscoveryCertificate

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

structure CertifiedClassifierState
    (SourceSpec PatternSpec LedgerPolicy : BHist -> Prop)
    (ClassifierSpec : BHist -> BHist -> Prop) : Prop where
  semantic_namecert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec

structure NameCertFiveRows where
  source : BHist
  pattern : BHist
  classifier : BHist
  stability : BHist
  ledger : BHist

def ClassifierEquivalentOn
    (Scope : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) : Prop :=
  forall {h k : BHist}, Scope h -> Scope k ->
    (ClassifierA h k -> ClassifierB h k) ∧
      (ClassifierB h k -> ClassifierA h k)

def ClassifierDisagreement
    (Scope : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) : Prop :=
  exists left right : BHist,
    Scope left ∧ Scope right ∧
      ClassifierA left right ∧ (ClassifierB left right -> False)

def ClassifierNonEquivalent
    (Scope : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) : Prop :=
  ClassifierDisagreement Scope ClassifierA ClassifierB ∨
    ClassifierDisagreement Scope ClassifierB ClassifierA

structure ScopeSeal where
  carrier : BHist -> Prop
  anchor : BHist
  anchored : carrier anchor

structure DiscoveryCost where
  amount : Nat
  positive : amount > 0

theorem costPositive (cost : DiscoveryCost) : cost.amount > 0 := by
  exact cost.positive

structure PositiveCostProtocol where
  cost : DiscoveryCost

structure StructuralDiscovery
    (BeforeSource BeforePattern BeforeLedger : BHist -> Prop)
    (BeforeClassifier : BHist -> BHist -> Prop)
    (AfterSource AfterPattern AfterLedger : BHist -> Prop)
    (AfterClassifier : BHist -> BHist -> Prop) where
  before_state :
    CertifiedClassifierState BeforeSource BeforePattern BeforeLedger BeforeClassifier
  after_state :
    CertifiedClassifierState AfterSource AfterPattern AfterLedger AfterClassifier
  before_rows : NameCertFiveRows
  after_rows : NameCertFiveRows
  scope : BHist -> Prop
  classifier_shift :
    ClassifierNonEquivalent scope BeforeClassifier AfterClassifier

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
    ClassifierNonEquivalent discovery.scope BeforeClassifier AfterClassifier := by
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
    exists rows : NameCertFiveRows, rows = discovery.after_rows := by
  exact Exists.intro discovery.after_rows rfl

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
    discovery.cost.amount > 0 := by
  exact costPositive discovery.cost

theorem positiveDiscovery_classifier_shift
    {BeforeSource BeforePattern BeforeLedger : BHist -> Prop}
    {BeforeClassifier : BHist -> BHist -> Prop}
    {AfterSource AfterPattern AfterLedger : BHist -> Prop}
    {AfterClassifier : BHist -> BHist -> Prop}
    (discovery :
      PositiveDiscovery
        BeforeSource BeforePattern BeforeLedger BeforeClassifier
        AfterSource AfterPattern AfterLedger AfterClassifier) :
    ClassifierNonEquivalent discovery.benefit.scope BeforeClassifier AfterClassifier := by
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

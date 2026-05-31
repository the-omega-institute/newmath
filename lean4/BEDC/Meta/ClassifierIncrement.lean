import BEDC.FKernel.NameCert

namespace BEDC.Meta.ClassifierIncrement

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

structure CertifiedClassifierState where
  SourceSpec : BHist -> Prop
  PatternSpec : BHist -> Prop
  LedgerPolicy : BHist -> Prop
  ClassifierSpec : BHist -> BHist -> Prop
  cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy ClassifierSpec

def ClassifierEquivalent
    (before after : CertifiedClassifierState) : Prop :=
  forall h k : BHist,
    before.ClassifierSpec h k -> after.ClassifierSpec h k

structure ClassifierIncrement where
  before : CertifiedClassifierState
  after : CertifiedClassifierState

def MechanicalComputation (inc : ClassifierIncrement) : Prop :=
  ClassifierEquivalent inc.before inc.after

def StructuralDiscovery (inc : ClassifierIncrement) : Prop :=
  Not (ClassifierEquivalent inc.before inc.after)

def PositiveDiscovery (inc : ClassifierIncrement) : Prop :=
  StructuralDiscovery inc

theorem mechanical_computation_not_discovery
    {inc : ClassifierIncrement} :
    MechanicalComputation inc -> Not (StructuralDiscovery inc) := by
  intro hMechanical hDiscovery
  exact hDiscovery hMechanical

theorem discovery_requires_namecert_and_ledger
    {inc : ClassifierIncrement} :
    PositiveDiscovery inc ->
      NameCert inc.after.SourceSpec inc.after.ClassifierSpec /\
        exists h : BHist, inc.after.LedgerPolicy h := by
  intro _
  exact And.intro inc.after.cert.core
    (semanticNameCert_ledger_policy_witness inc.after.cert)

theorem discovery_carries_semantic_certificate
    {inc : ClassifierIncrement} :
    PositiveDiscovery inc ->
      SemanticNameCert
        inc.after.SourceSpec
        inc.after.PatternSpec
        inc.after.LedgerPolicy
        inc.after.ClassifierSpec := by
  intro _
  exact inc.after.cert

end BEDC.Meta.ClassifierIncrement

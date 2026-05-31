import BEDC.Meta.DiscoveryCertificate
import BEDC.Meta.DiscoveryCertificateExample
import BEDC.GroundCompiler.ChannelEncoding

namespace BEDC.Meta.DisagreementSupport

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.DiscoveryCertificate
open BEDC.Meta.DiscoveryCertificateExample

structure StableSemanticSeparation
    (Observable : BHist -> Prop) (left right : BHist) where
  respects_hsame : forall {h k : BHist}, hsame h k -> Observable h -> Observable k
  left_observed : Observable left
  right_refuted : Observable right -> False

structure ObservableWitness where
  Observable : BHist -> Prop
  observable_namecert : NameCert Observable hsame

inductive SupportFamily where
  | classifier
  | decode (witness : ObservableWitness)
  | readback (witness : ObservableWitness)
  | ledger (witness : ObservableWitness)
  | role (witness : ObservableWitness)

def SupportFamily.Observable (family : SupportFamily) : BHist -> Prop :=
  match family with
  | SupportFamily.classifier => fun _h => False
  | SupportFamily.decode witness => witness.Observable
  | SupportFamily.readback witness => witness.Observable
  | SupportFamily.ledger witness => witness.Observable
  | SupportFamily.role witness => witness.Observable

inductive ObservableSupportFamily : SupportFamily -> Prop where
  | decode (witness : ObservableWitness) :
      ObservableSupportFamily (SupportFamily.decode witness)
  | readback (witness : ObservableWitness) :
      ObservableSupportFamily (SupportFamily.readback witness)
  | ledger (witness : ObservableWitness) :
      ObservableSupportFamily (SupportFamily.ledger witness)
  | role (witness : ObservableWitness) :
      ObservableSupportFamily (SupportFamily.role witness)

def SupportFamily.observableNameCert
    (family : SupportFamily) (observable : ObservableSupportFamily family) :
    NameCert (SupportFamily.Observable family) hsame :=
  match family, observable with
  | SupportFamily.decode witness, ObservableSupportFamily.decode _ =>
      witness.observable_namecert
  | SupportFamily.readback witness, ObservableSupportFamily.readback _ =>
      witness.observable_namecert
  | SupportFamily.ledger witness, ObservableSupportFamily.ledger _ =>
      witness.observable_namecert
  | SupportFamily.role witness, ObservableSupportFamily.role _ =>
      witness.observable_namecert

inductive IndependentSupportFamily : SupportFamily -> SupportFamily -> Prop where
  | classifier_decode (witness : ObservableWitness) :
      IndependentSupportFamily SupportFamily.classifier (SupportFamily.decode witness)
  | classifier_readback (witness : ObservableWitness) :
      IndependentSupportFamily SupportFamily.classifier (SupportFamily.readback witness)
  | classifier_ledger (witness : ObservableWitness) :
      IndependentSupportFamily SupportFamily.classifier (SupportFamily.ledger witness)
  | classifier_role (witness : ObservableWitness) :
      IndependentSupportFamily SupportFamily.classifier (SupportFamily.role witness)

structure DisagreementSupport
    (Scope : BHist -> Prop)
    (SourceA SourceB : BHist -> Prop)
    (ClassifierA ClassifierB : BHist -> BHist -> Prop) where
  disagreement : ClassifierDisagreement Scope SourceA SourceB ClassifierA ClassifierB
  source_family : SupportFamily
  observable_family : SupportFamily
  family_independent : IndependentSupportFamily source_family observable_family
  observable_family_supported : ObservableSupportFamily observable_family
  observable_namecert :
    NameCert (SupportFamily.Observable observable_family) hsame
  semantic_separation :
    StableSemanticSeparation
      (SupportFamily.Observable observable_family) disagreement.left disagreement.right

def ReadbackRow (h : BHist) : Prop :=
  hsame h BHist.Empty ∧
    Decode (FlowEncoding [[BMark.b0]]) = some [[BMark.b0]]

def ReadbackWitnessRow (h : BHist) : Prop :=
  hsame h (BHist.e0 BHist.Empty)

def SupportSource (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ hsame h (BHist.e0 BHist.Empty)

def SupportScope (h : BHist) : Prop :=
  SupportSource h

def SupportBeforeClassifier (left right : BHist) : Prop :=
  hsame left BHist.Empty ∧ hsame right (BHist.e0 BHist.Empty)

def SupportAfterClassifier (left right : BHist) : Prop :=
  hsame left (BHist.e0 BHist.Empty) ∧ hsame right BHist.Empty

def readbackRowNameCert : NameCert ReadbackRow hsame where
  carrier_inhabited :=
    Exists.intro BHist.Empty (And.intro rfl (flow_level_round_trip [[BMark.b0]]))
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
    intro h k same source
    cases same
    exact source

def readbackRowWitness : ObservableWitness where
  Observable := ReadbackRow
  observable_namecert := readbackRowNameCert

def readbackDecodeFamily : SupportFamily :=
  SupportFamily.decode readbackRowWitness

def supportDisagreement :
    ClassifierDisagreement
      SupportScope SupportSource SupportSource
      SupportBeforeClassifier SupportAfterClassifier where
  left := BHist.Empty
  right := BHist.e0 BHist.Empty
  left_scope := Or.inl rfl
  right_scope := Or.inr rfl
  left_source_a := Or.inl rfl
  right_source_a := Or.inr rfl
  left_source_b := Or.inl rfl
  right_source_b := Or.inr rfl
  positive := And.intro rfl rfl
  negative := by
    intro after
    exact not_hsame_emp_e0 after.left

def supportSemanticSeparation :
    StableSemanticSeparation
      (SupportFamily.Observable readbackDecodeFamily)
      supportDisagreement.left supportDisagreement.right where
  respects_hsame := by
    intro h k same observed
    cases same
    exact observed
  left_observed := And.intro rfl (flow_level_round_trip [[BMark.b0]])
  right_refuted := by
    intro observed
    exact not_hsame_e0_empty observed.left

def supportDisagreementSupport :
    DisagreementSupport
      SupportScope SupportSource SupportSource
      SupportBeforeClassifier SupportAfterClassifier where
  disagreement := supportDisagreement
  source_family := SupportFamily.classifier
  observable_family := readbackDecodeFamily
  family_independent := IndependentSupportFamily.classifier_decode readbackRowWitness
  observable_family_supported := ObservableSupportFamily.decode readbackRowWitness
  observable_namecert :=
    SupportFamily.observableNameCert
      readbackDecodeFamily
      (ObservableSupportFamily.decode readbackRowWitness)
  semantic_separation := supportSemanticSeparation

def smokeShiftDeltaLedger_support :
    DisagreementSupport
      SmokeScope SmokeSource SmokeSource
      SmokeClassifierAfter SmokeClassifierBefore where
  disagreement := smokeDisagreement
  source_family := SupportFamily.classifier
  observable_family := readbackDecodeFamily
  family_independent := IndependentSupportFamily.classifier_decode readbackRowWitness
  observable_family_supported := ObservableSupportFamily.decode readbackRowWitness
  observable_namecert :=
    SupportFamily.observableNameCert
      readbackDecodeFamily
      (ObservableSupportFamily.decode readbackRowWitness)
  semantic_separation := by
    exact supportSemanticSeparation

end BEDC.Meta.DisagreementSupport

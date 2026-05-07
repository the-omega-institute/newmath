import BEDC.Derived.BanachUp
import BEDC.Derived.LinearMapUp
import BEDC.Derived.MetricUp.Transport
import BEDC.Derived.RealUp.Core
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FunctionalAnalysisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.LinearMapUp
open BEDC.Derived.MetricUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp

def FunctionalAnalysisDualPointwiseClassifier
    (ScalarClassifier : BHist -> BHist -> Prop) (f g : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ LinearMapSingletonCarrier g ∧
    forall {x : BHist}, BanachSingletonCarrier x ->
      ScalarClassifier (LinearMapSingletonEval f x) (LinearMapSingletonEval g x)

def FunctionalAnalysisBoundedOperatorRow
    (f source target bound ledger : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ BanachSingletonCarrier source ∧
    BanachSingletonCarrier target ∧
      RealConstantHistoryClassifier bound (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        Cont source target ledger

theorem FunctionalAnalysisBoundedOperatorRow_visible_ledger
    {f source target bound ledger : BHist} :
    FunctionalAnalysisBoundedOperatorRow f source target bound ledger ->
      LinearMapSingletonCarrier f ∧ BanachSingletonCarrier source ∧
        BanachSingletonCarrier target ∧
          RealConstantHistoryClassifier bound (BHist.e1 (BHist.e1 BHist.Empty)) ∧
            Cont source target ledger ∧ UnaryHistory ledger := by
  intro row
  have sourceUnary : UnaryHistory source := by
    exact unary_transport unary_empty (hsame_symm row.right.left.left)
  have targetUnary : UnaryHistory target := by
    exact unary_transport unary_empty (hsame_symm row.right.right.left.left)
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary targetUnary row.right.right.right.right
  exact And.intro row.left
    (And.intro row.right.left
      (And.intro row.right.right.left
        (And.intro row.right.right.right.left
          (And.intro row.right.right.right.right ledgerUnary))))

theorem FunctionalAnalysisBoundedOperatorRow_ledger_hsame_transport
    {f source target bound ledger source' target' ledger' : BHist} :
    FunctionalAnalysisBoundedOperatorRow f source target bound ledger ->
      hsame source source' -> hsame target target' -> Cont source' target' ledger' ->
        FunctionalAnalysisBoundedOperatorRow f source' target' bound ledger' ∧
          hsame ledger ledger' := by
  intro row sameSource sameTarget ledgerCont'
  have sourceVec' : VecSpaceSingletonCarrier source' :=
    hsame_trans (hsame_symm sameSource) row.right.left.left
  have sourceMetricFields' :
      UnaryHistory source' ∧ UnaryHistory BHist.Empty ∧ UnaryHistory BHist.Empty ∧
        Cont source' BHist.Empty BHist.Empty :=
    MetricDistanceWitness_hsame_fields_transport sameSource (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) row.right.left.right
  have sourceBanach' : BanachSingletonCarrier source' :=
    And.intro sourceVec'
      (And.intro sourceMetricFields'.left
        (And.intro sourceMetricFields'.right.left
          (And.intro sourceMetricFields'.right.right.left
            sourceMetricFields'.right.right.right)))
  have targetVec' : VecSpaceSingletonCarrier target' :=
    hsame_trans (hsame_symm sameTarget) row.right.right.left.left
  have targetMetricFields' :
      UnaryHistory target' ∧ UnaryHistory BHist.Empty ∧ UnaryHistory BHist.Empty ∧
        Cont target' BHist.Empty BHist.Empty :=
    MetricDistanceWitness_hsame_fields_transport sameTarget (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) row.right.right.left.right
  have targetBanach' : BanachSingletonCarrier target' :=
    And.intro targetVec'
      (And.intro targetMetricFields'.left
        (And.intro targetMetricFields'.right.left
          (And.intro targetMetricFields'.right.right.left
            targetMetricFields'.right.right.right)))
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSource sameTarget row.right.right.right.right ledgerCont'
  exact And.intro
    (And.intro row.left
      (And.intro sourceBanach'
        (And.intro targetBanach' (And.intro row.right.right.right.left ledgerCont'))))
    sameLedger

theorem FunctionalAnalysisBoundedLinearOperator_norm_bound_stable
    {T : BHist -> BHist} {K K' ledger ledger' : BHist} :
    BanachSingletonBoundedLinearOperator T K ledger -> hsame K K' -> hsame ledger ledger' ->
      BanachSingletonBoundedLinearOperator T K' ledger' ∧ hsame K' BHist.Empty := by
  intro bounded sameK sameLedger
  have boundK : hsame K BHist.Empty := bounded.left
  have boundK' : hsame K' BHist.Empty := hsame_trans (hsame_symm sameK) boundK
  have ledgerNonempty' : hsame ledger' BHist.Empty -> False := by
    intro ledgerEmpty'
    exact bounded.right.left (hsame_trans sameLedger ledgerEmpty')
  have transported :
      BanachSingletonBoundedLinearOperator T K' ledger' :=
    And.intro boundK' (And.intro ledgerNonempty' bounded.right.right)
  exact And.intro transported boundK'

theorem FunctionalAnalysisDualPointwiseClassifier_equivalence_rows
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    (scalarEval : forall {f x : BHist}, LinearMapSingletonCarrier f -> BanachSingletonCarrier x ->
      ScalarCarrier (LinearMapSingletonEval f x)) :
    (forall {f : BHist}, LinearMapSingletonCarrier f ->
      FunctionalAnalysisDualPointwiseClassifier ScalarClassifier f f) ∧
      (forall {f g : BHist}, FunctionalAnalysisDualPointwiseClassifier ScalarClassifier f g ->
        FunctionalAnalysisDualPointwiseClassifier ScalarClassifier g f) ∧
        (forall {f g h : BHist}, FunctionalAnalysisDualPointwiseClassifier ScalarClassifier f g ->
          FunctionalAnalysisDualPointwiseClassifier ScalarClassifier g h ->
            FunctionalAnalysisDualPointwiseClassifier ScalarClassifier f h) := by
  constructor
  · intro f carrierF
    exact And.intro carrierF
      (And.intro carrierF
        (by
          intro x carrierX
          exact NameCert.equiv_refl scalarCert (scalarEval carrierF carrierX)))
  · constructor
    · intro f g classified
      exact And.intro classified.right.left
        (And.intro classified.left
          (by
            intro x carrierX
            exact NameCert.equiv_symm scalarCert (classified.right.right carrierX)))
    · intro f g h classifiedFG classifiedGH
      exact And.intro classifiedFG.left
        (And.intro classifiedGH.right.left
          (by
            intro x carrierX
            exact NameCert.equiv_trans scalarCert
              (classifiedFG.right.right carrierX) (classifiedGH.right.right carrierX)))

end BEDC.Derived.FunctionalAnalysisUp

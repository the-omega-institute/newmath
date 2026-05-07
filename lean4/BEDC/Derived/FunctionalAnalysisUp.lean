import BEDC.Derived.BanachUp
import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.FunctionalAnalysisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.BanachUp
open BEDC.Derived.LinearMapUp

def FunctionalAnalysisDualPointwiseClassifier
    (ScalarClassifier : BHist -> BHist -> Prop) (f g : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ LinearMapSingletonCarrier g ∧
    forall {x : BHist}, BanachSingletonCarrier x ->
      ScalarClassifier (LinearMapSingletonEval f x) (LinearMapSingletonEval g x)

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

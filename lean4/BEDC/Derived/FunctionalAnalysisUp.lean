import BEDC.Derived.BanachUp
import BEDC.Derived.LinearMapUp
import BEDC.Derived.RealUp.Core
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FunctionalAnalysisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.LinearMapUp
open BEDC.Derived.RealUp

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

end BEDC.Derived.FunctionalAnalysisUp

import BEDC.Derived.BanachUp

namespace BEDC.Derived.FunctionalAnalysisUp

open BEDC.FKernel.Hist
open BEDC.Derived.BanachUp

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

import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.HypothesisTestUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def HypothesisTestDecisionCarrier (nullHyp altHyp sample statistic threshold reject accept typeI
    typeII ledger endpoint : BHist) : Prop :=
  Cont sample statistic threshold ∧ Cont threshold reject typeI ∧
    Cont threshold accept typeII ∧ Cont typeI typeII ledger ∧
      hsame endpoint (append ledger (append nullHyp altHyp))

theorem HypothesisTestDecisionCarrier_distribution_consumer_boundary
    {nullHyp altHyp sample statistic threshold reject accept typeI typeII ledger
      endpoint : BHist} :
    HypothesisTestDecisionCarrier nullHyp altHyp sample statistic threshold reject accept typeI
        typeII ledger endpoint →
      Cont sample statistic threshold ∧ Cont threshold reject typeI ∧
        Cont threshold accept typeII ∧ Cont typeI typeII ledger ∧
          hsame endpoint (append ledger (append nullHyp altHyp)) := by
  intro carrier
  constructor
  · exact carrier.left
  · constructor
    · exact carrier.right.left
    · constructor
      · exact carrier.right.right.left
      · constructor
        · exact carrier.right.right.right.left
        · exact carrier.right.right.right.right

end BEDC.Derived.HypothesisTestUp

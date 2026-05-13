import BEDC.FKernel.Cont

namespace BEDC.Derived.AxiomQueryLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def AxiomQueryLedgerCarrier
    (declaration query forbidden verdict transport route provenance name : BHist) :
    Prop :=
  Cont declaration query verdict ∧
    Cont query forbidden transport ∧
      hsame route (append transport verdict) ∧
        hsame provenance (append route name) ∧
          hsame name declaration ∧ hsame name query

theorem AxiomQueryLedgerCarrier_query_soundness
    {declaration query queryPrime forbidden verdict verdictPrime transport route provenance
      name : BHist} :
    AxiomQueryLedgerCarrier declaration query forbidden verdict transport route provenance name →
      hsame query queryPrime →
        hsame verdict verdictPrime →
          Cont declaration queryPrime verdictPrime := by
  intro carrier sameQuery sameVerdict
  cases sameQuery
  cases sameVerdict
  exact carrier.left

end BEDC.Derived.AxiomQueryLedgerUp

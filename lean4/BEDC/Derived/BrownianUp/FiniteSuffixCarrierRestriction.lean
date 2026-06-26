import BEDC.Derived.BrownianUp

namespace BEDC.Derived.BrownianUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BrownianStepContinuityClassifier_finite_suffix_carrier_restriction
    {martingale continuous time path step normal provenance ledger suffixMartingale
      suffixContinuous suffixTime suffixPath suffixStep suffixNormal suffixProvenance
      suffixLedger suffixBoundary : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      hsame martingale suffixMartingale ->
        hsame continuous suffixContinuous ->
          hsame time suffixTime ->
            hsame path suffixPath ->
              hsame normal suffixNormal ->
                Cont suffixContinuous suffixPath suffixStep ->
                  Cont suffixMartingale suffixStep suffixProvenance ->
                    Cont suffixProvenance suffixNormal suffixLedger ->
                      Cont suffixTime suffixLedger suffixBoundary ->
                        BrownianStepContinuityClassifier suffixMartingale suffixContinuous
                            suffixTime suffixPath suffixStep suffixNormal suffixProvenance
                            suffixLedger ∧
                          UnaryHistory suffixBoundary ∧ hsame step suffixStep ∧
                            hsame provenance suffixProvenance ∧ hsame ledger suffixLedger ∧
                              hsame suffixBoundary (append suffixTime suffixLedger) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classified sameMartingale sameContinuous sameTime samePath sameNormal suffixStepRow
    suffixProvenanceRow suffixLedgerRow suffixBoundaryRow
  have stable :
      BrownianStepContinuityClassifier suffixMartingale suffixContinuous suffixTime suffixPath
          suffixStep suffixNormal suffixProvenance suffixLedger ∧
        hsame step suffixStep ∧ hsame provenance suffixProvenance ∧ hsame ledger suffixLedger :=
    BrownianStepContinuityClassifier_classifier_stability classified sameMartingale sameContinuous
      sameTime samePath sameNormal suffixStepRow suffixProvenanceRow suffixLedgerRow
  have suffixBoundaryUnary : UnaryHistory suffixBoundary :=
    unary_cont_closed (unary_transport classified.right.right.left sameTime)
      (unary_cont_closed
        (unary_cont_closed (unary_transport classified.left sameMartingale)
          (unary_cont_closed (unary_transport classified.right.left sameContinuous)
            (unary_transport classified.right.right.right.left samePath) suffixStepRow)
          suffixProvenanceRow)
        (unary_transport classified.right.right.right.right.left sameNormal) suffixLedgerRow)
      suffixBoundaryRow
  exact And.intro stable.left
    (And.intro suffixBoundaryUnary
      (And.intro stable.right.left
        (And.intro stable.right.right.left
          (And.intro stable.right.right.right suffixBoundaryRow))))

end BEDC.Derived.BrownianUp

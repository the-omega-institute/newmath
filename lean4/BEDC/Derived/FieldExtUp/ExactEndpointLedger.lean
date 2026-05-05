import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.RatUp
open BEDC.Derived.VecSpaceUp

def FieldExtRatReflexive_exactness_ledger_interface
    (h k r m out product : BHist) : Prop :=
  RatHistoryClassifier h k ∧ RatHistoryCarrier r ∧ RatHistoryCarrier m ∧
    Cont r m product ∧ Cont (FieldExtSingletonEmbedding r) m out ∧
      RatHistoryClassifier (FieldExtSingletonEmbedding h) h ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding k) k ∧
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier out product

theorem FieldExtSingletonLedgerPolicy_exact_endpoint_ledger {h : BHist} :
    FieldExtSingletonLedgerPolicy h ->
      FieldSingletonClassifier (FieldExtSingletonEmbedding h) BHist.Empty ∧
        VecSpaceSingletonClassifier h BHist.Empty ∧
          FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h) := by
  intro policy
  have rows := FieldExtSingletonLedgerPolicy_carrier_coincidence policy
  have embeddedCarrier : FieldSingletonCarrier (FieldExtSingletonEmbedding h) :=
    rows.right.right.left
  have embeddedEndpoint : FieldSingletonClassifier (FieldExtSingletonEmbedding h) BHist.Empty :=
    And.intro embeddedCarrier
      (And.intro (hsame_refl BHist.Empty) embeddedCarrier)
  have vecEndpoint : VecSpaceSingletonClassifier h BHist.Empty :=
    And.intro rows.right.left
      (And.intro (hsame_refl BHist.Empty) rows.right.left)
  exact And.intro embeddedEndpoint (And.intro vecEndpoint rows.right.right)

end BEDC.Derived.FieldExtUp

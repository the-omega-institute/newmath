import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RatUp_StdBridge {raw visible : BHist} :
    RatHistoryLedgerPolicy raw visible ->
      RatHistoryClassifier raw visible ∧ PositiveUnaryDenominator raw ∧
        PositiveUnaryDenominator visible ∧
          SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
            RatHistoryClassifier := by
  intro ledger
  have rawPositive : PositiveUnaryDenominator raw :=
    RatHistoryCarrier_iff_positive_denominator.mp ledger.left
  have visiblePositive : PositiveUnaryDenominator visible :=
    RatHistoryCarrier_iff_positive_denominator.mp
      (RatHistoryLedgerPolicy_visible_carrier ledger)
  exact And.intro (RatHistoryLedgerPolicy_raw_visible_classifier ledger)
    (And.intro rawPositive
      (And.intro visiblePositive rat_history_semantic_name_certificate))

theorem RatHistoryLedgerPolicy_two_sided_endpoint_classifier_equivalence
    {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v ->
      ((RatHistoryClassifier rho w ↔ RatHistoryClassifier v w) ∧
        (RatHistoryClassifier w rho ↔ RatHistoryClassifier w v) ∧
          PositiveUnaryDenominator rho ∧ PositiveUnaryDenominator v ∧
            (RatHistoryClassifier v w -> PositiveUnaryDenominator w) ∧
              (RatHistoryClassifier w v -> PositiveUnaryDenominator w)) := by
  intro ledger
  have sameRhoV : hsame rho v := ledger.right
  have rhoPositive : PositiveUnaryDenominator rho :=
    RatHistoryCarrier_iff_positive_denominator.mp ledger.left
  have vPositive : PositiveUnaryDenominator v :=
    RatHistoryCarrier_iff_positive_denominator.mp
      (RatHistoryLedgerPolicy_visible_carrier ledger)
  constructor
  · constructor
    · intro classified
      exact RatHistoryClassifier_hsame_transport sameRhoV (hsame_refl w) classified
    · intro classified
      exact RatHistoryClassifier_hsame_transport (hsame_symm sameRhoV) (hsame_refl w)
        classified
  · constructor
    · constructor
      · intro classified
        exact RatHistoryClassifier_hsame_transport (hsame_refl w) sameRhoV classified
      · intro classified
        exact RatHistoryClassifier_hsame_transport (hsame_refl w) (hsame_symm sameRhoV)
          classified
    · exact And.intro rhoPositive
        (And.intro vPositive
          (And.intro
            (fun classified =>
              RatHistoryCarrier_iff_positive_denominator.mp classified.right.left)
            (fun classified =>
              RatHistoryCarrier_iff_positive_denominator.mp classified.left)))

end BEDC.Derived.RatUp

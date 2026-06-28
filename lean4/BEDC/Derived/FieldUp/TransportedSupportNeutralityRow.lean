import BEDC.Derived.FieldUp.ContextualActionPair

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RatupFieldupTransportedSupportNeutralityRow
    {p q p' q' h l r l' r' s t s' t' : BHist} :
    hsame p BHist.Empty →
      hsame q BHist.Empty →
        hsame p' BHist.Empty →
          hsame q' BHist.Empty →
            RatDenomUnitCarrier h →
              RatDenomUnitClassifier l s →
                RatDenomUnitClassifier r t →
                  RatDenomUnitClassifier l' s' →
                    RatDenomUnitClassifier r' t' →
                      RatHistoryCarrier
                        (RatDenomUnitContextualAction p' q' l' r'
                          (RatDenomUnitContextualAction p q l r h)) →
                        RatDenomUnitCarrier
                          (RatDenomUnitContextualAction p' q' s' t'
                            (RatDenomUnitContextualAction p q s t h)) ∧
                          (RatHistoryCarrier
                              (RatDenomUnitContextualAction p' q' s' t'
                                (RatDenomUnitContextualAction p q s t h)) ↔
                            RatHistoryCarrier
                              (RatDenomUnitContextualAction p' q' l' r'
                                (RatDenomUnitContextualAction p q l r h))) := by
  -- BEDC touchpoint anchor: BHist hsame RatDenomUnitCarrier RatHistoryCarrier
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL'
    classifiedR' originalSupport
  have transported :=
    field_rat_denominator_contextual_action_pair_transport_carrier_support
      sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  exact ⟨transported.right.left, Iff.symm transported.right.right⟩

end BEDC.Derived.FieldUp

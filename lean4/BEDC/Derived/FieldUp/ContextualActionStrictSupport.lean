import BEDC.Derived.FieldUp.ContextualActionEmptyContextTransport

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_strict_support_endpoint_empty_absurd
    {p q p' q' h l r l' r' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier l ->
        RatDenomUnitCarrier r -> RatDenomUnitCarrier l' -> RatDenomUnitCarrier r' ->
          RatHistoryCarrier h ->
            hsame
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h))
              BHist.Empty -> False := by
  intro sameP sameQ sameP' sameQ' carrierH carrierL carrierR carrierL' carrierR' ratH
    nestedEmpty
  have laws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH carrierL carrierR carrierL' carrierR'
  have nestedRat :
      RatHistoryCarrier
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h)) :=
    Iff.mpr laws.right.right (Or.inr (Or.inr (Or.inl ratH)))
  exact RatHistoryCarrier_not_empty nestedRat nestedEmpty

theorem RatDenomUnitContextualAction_empty_pair_strict_support_commutes
    {h l r l' r' : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier l -> RatDenomUnitCarrier r ->
      RatDenomUnitCarrier l' -> RatDenomUnitCarrier r' ->
        (RatHistoryCarrier
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l' r'
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l r h)) ↔
          RatHistoryCarrier
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l r
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l' r' h))) := by
  intro carrierH carrierL carrierR carrierL' carrierR'
  have classified :=
    RatDenomUnitContextualAction_empty_pair_commutes carrierH carrierL carrierR carrierL'
      carrierR'
  constructor
  · intro leftRat
    exact RatHistoryCarrier_hsame_transport classified.right.right leftRat
  · intro rightRat
    exact RatHistoryCarrier_hsame_transport (hsame_symm classified.right.right) rightRat

theorem RatDenomUnitContextualAction_empty_pair_adjacent_swap_coherence
    {h l0 r0 l1 r1 l2 r2 : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitCarrier l0 -> RatDenomUnitCarrier r0 ->
      RatDenomUnitCarrier l1 -> RatDenomUnitCarrier r1 -> RatDenomUnitCarrier l2 ->
        RatDenomUnitCarrier r2 ->
          RatDenomUnitClassifier
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1 h))) ∧
          (RatHistoryCarrier
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))) ↔
            RatHistoryCarrier
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1 h)))) := by
  intro carrierH carrierL0 carrierR0 carrierL1 carrierR1 carrierL2 carrierR2
  have innerClassified :
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1 h)) :=
    RatDenomUnitContextualAction_empty_pair_commutes carrierH carrierL0 carrierR0
      carrierL1 carrierR1
  have outerClassified :
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1 h))) :=
    RatDenomUnitContextualAction_empty_context_hsame_transport carrierL2 carrierR2
      innerClassified
  constructor
  · exact outerClassified
  · constructor
    · intro leftRat
      exact RatHistoryCarrier_hsame_transport outerClassified.right.right leftRat
    · intro rightRat
      exact RatHistoryCarrier_hsame_transport (hsame_symm outerClassified.right.right) rightRat

end BEDC.Derived.FieldUp

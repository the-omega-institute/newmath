import BEDC.Derived.FieldUp.ContextualActionEmptyContextTransport

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem RatDenomUnitContextualAction_threefold_pair_support_transport
    {h l0 r0 l1 r1 l2 r2 s0 t0 s1 t1 s2 t2 : BHist} :
    RatDenomUnitCarrier h -> RatDenomUnitClassifier l0 s0 ->
      RatDenomUnitClassifier r0 t0 -> RatDenomUnitClassifier l1 s1 ->
        RatDenomUnitClassifier r1 t1 -> RatDenomUnitClassifier l2 s2 ->
          RatDenomUnitClassifier r2 t2 ->
            (RatHistoryCarrier
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))) <->
              RatHistoryCarrier
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty s2 t2
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty s1 t1
                    (RatDenomUnitContextualAction BHist.Empty BHist.Empty s0 t0 h)))) := by
  intro carrierH classifiedL0 classifiedR0 classifiedL1 classifiedR1 classifiedL2 classifiedR2
  have classifiedFirstTwo :
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty s1 t1
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty s0 t0 h)) :=
    RatDenomUnitContextualAction_pair_classifier_transport (hsame_refl BHist.Empty)
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
      carrierH classifiedL0 classifiedR0 classifiedL1 classifiedR1
  have classifiedThree :
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty l2 r2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty s2 t2
          (RatDenomUnitContextualAction BHist.Empty BHist.Empty s1 t1
            (RatDenomUnitContextualAction BHist.Empty BHist.Empty s0 t0 h))) :=
    by
      have classifiedLeftCore :
          RatDenomUnitClassifier
            (append l2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h)))
            (append s2
              (RatDenomUnitContextualAction BHist.Empty BHist.Empty s1 t1
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty s0 t0 h))) :=
        RatDenomUnitClassifier_continuation_closed classifiedL2 classifiedFirstTwo
          (cont_intro rfl) (cont_intro rfl)
      have classifiedCore :
          RatDenomUnitClassifier
            (append
              (append l2
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty l1 r1
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty l0 r0 h))) r2)
            (append
              (append s2
                (RatDenomUnitContextualAction BHist.Empty BHist.Empty s1 t1
                  (RatDenomUnitContextualAction BHist.Empty BHist.Empty s0 t0 h))) t2) :=
        RatDenomUnitClassifier_continuation_closed classifiedLeftCore classifiedR2
          (cont_intro rfl) (cont_intro rfl)
      exact
        (RatDenomUnitClassifier_empty_context_iff (hsame_refl BHist.Empty)
          (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)).mpr
          classifiedCore
  constructor
  · intro leftSupport
    exact RatHistoryCarrier_hsame_transport classifiedThree.right.right leftSupport
  · intro rightSupport
    exact RatHistoryCarrier_hsame_transport (hsame_symm classifiedThree.right.right)
      rightSupport

end BEDC.Derived.FieldUp

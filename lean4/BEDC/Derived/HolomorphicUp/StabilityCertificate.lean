import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem HolomorphicOpenDiskCarrier_stability_certificate
    {center center' radius radius' point point' extra extendedRadius : BHist} :
    HolomorphicOpenDiskCarrier center radius point -> hsame center center' ->
      hsame radius radius' -> hsame point point' -> UnaryHistory extra ->
        Cont radius' extra extendedRadius ->
          HolomorphicOpenDiskWitnessed center' extendedRadius point' ∧
            ∃ gap : BHist, ∃ extendedGap : BHist,
              UnaryHistory gap ∧ UnaryHistory extendedGap ∧ Cont point' gap radius' ∧
                Cont gap extra extendedGap ∧ Cont point' extendedGap extendedRadius := by
  intro carrier sameCenter sameRadius samePoint extraUnary radiusExtension
  cases carrier with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier gapWitness =>
              have centerUnary : UnaryHistory center :=
                BEDC.Derived.ComplexUp.ComplexHistoryCarrier_unary centerCarrier
              have radiusPositive : BEDC.Derived.RatUp.PositiveUnaryDenominator radius :=
                BEDC.Derived.RatUp.RatHistoryCarrier_iff_positive_denominator.mp
                  radiusCarrier
              have radiusUnary : UnaryHistory radius :=
                (BEDC.Derived.RatUp.PositiveUnaryDenominator_unary_and_nonempty
                  radiusPositive).left
              have pointUnary : UnaryHistory point :=
                BEDC.Derived.ComplexUp.ComplexHistoryCarrier_unary pointCarrier
              cases gapWitness with
              | intro gap gapData =>
                  cases gapData with
                  | intro gapUnary gapRest =>
                      cases gapRest with
                      | intro _gapPrefix pointGap =>
                          have centerUnary' : UnaryHistory center' :=
                            unary_transport centerUnary sameCenter
                          have radiusUnary' : UnaryHistory radius' :=
                            unary_transport radiusUnary sameRadius
                          have pointUnary' : UnaryHistory point' :=
                            unary_transport pointUnary samePoint
                          have pointGap' : Cont point' gap radius' :=
                            cont_hsame_transport samePoint (hsame_refl gap) sameRadius pointGap
                          have middle := cont_assoc_middle_exists pointGap' radiusExtension
                          cases middle with
                          | intro extendedGap extendedData =>
                              cases extendedData with
                              | intro gapExtra pointExtended =>
                                  have extendedGapUnary : UnaryHistory extendedGap :=
                                    unary_cont_closed gapUnary extraUnary gapExtra
                                  exact And.intro
                                    (And.intro centerUnary'
                                      (And.intro
                                        (unary_cont_closed radiusUnary' extraUnary
                                          radiusExtension)
                                        (And.intro pointUnary'
                                          (Exists.intro extendedGap
                                            (And.intro extendedGapUnary pointExtended)))))
                                    (Exists.intro gap
                                      (Exists.intro extendedGap
                                        (And.intro gapUnary
                                          (And.intro extendedGapUnary
                                            (And.intro pointGap'
                                              (And.intro gapExtra pointExtended))))))

end BEDC.Derived.HolomorphicUp

import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ComplexTopologyOpenDiskGap (center radius point gap : BHist) : Prop :=
  ComplexHistoryCarrier center ∧ UnaryHistory radius ∧ ComplexHistoryCarrier point ∧
    UnaryHistory gap ∧ Cont point gap radius

theorem ComplexTopologyOpenDiskGap_hsame_transport
    {center center' radius radius' point point' gap gap' : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap ->
      ComplexHistoryClassifier center center' -> hsame radius radius' ->
        ComplexHistoryClassifier point point' -> hsame gap gap' ->
          ComplexTopologyOpenDiskGap center' radius' point' gap' ∧ Cont point' gap' radius' := by
  intro disk centerClass sameRadius pointClass sameGap
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro _pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  cases centerClass with
                  | intro _centerSource centerRest =>
                      cases centerRest with
                      | intro centerTarget sameCenter =>
                          cases pointClass with
                          | intro _pointSource pointRest =>
                              cases pointRest with
                              | intro pointTarget samePoint =>
                                  have radiusCarrier' : UnaryHistory radius' :=
                                    unary_transport radiusCarrier sameRadius
                                  have gapCarrier' : UnaryHistory gap' :=
                                    unary_transport gapCarrier sameGap
                                  have pointGap' : Cont point' gap' radius' :=
                                    cont_hsame_transport samePoint sameGap sameRadius pointGap
                                  exact And.intro
                                    (And.intro centerTarget
                                      (And.intro radiusCarrier'
                                        (And.intro pointTarget
                                          (And.intro gapCarrier' pointGap'))))
                                    pointGap'

end BEDC.Derived.ComplexTopologyUp

import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp
import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.HolomorphicUp

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

theorem ComplexTopologyOpenDisk_point_radius_suffix_closed {z0 r z extra r' z' : BHist} :
    OpenDisk z0 r z -> UnaryHistory extra -> Cont r extra r' -> Cont z extra z' ->
      OpenDisk z0 r' z' ∧ ∃ gap : BHist,
        UnaryHistory gap ∧ Cont gap z r ∧ Cont gap z' r' := by
  intro disk extraUnary radiusExtra pointExtra
  cases disk with
  | intro centerCarrier diskRest =>
      cases diskRest with
      | intro radiusUnary diskRest =>
          cases diskRest with
          | intro pointCarrier gapWitness =>
              cases gapWitness with
              | intro gap gapData =>
                  cases gapData with
                  | intro gapUnary gapPoint =>
                      have radiusUnary' : UnaryHistory r' :=
                        unary_cont_closed radiusUnary extraUnary radiusExtra
                      have shiftedPointCarrier : ComplexHistoryCarrier z' :=
                        BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport pointExtra.symm
                          (ComplexHistoryCarrier_append_unary_closed pointCarrier extraUnary)
                      have shiftedGapPoint : Cont gap z' r' := by
                        cases gapPoint
                        cases pointExtra
                        cases radiusExtra
                        exact append_assoc gap z extra
                      exact And.intro
                        (And.intro centerCarrier
                          (And.intro radiusUnary'
                            (And.intro shiftedPointCarrier
                              (Exists.intro gap (And.intro gapUnary shiftedGapPoint)))))
                        (Exists.intro gap
                          (And.intro gapUnary (And.intro gapPoint shiftedGapPoint)))

theorem ComplexTopologyOpenDiskGap_radius_extension_closed
    {center radius point gap extra radiusOut gapOut : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> UnaryHistory extra ->
      Cont radius extra radiusOut -> Cont gap extra gapOut ->
        ComplexTopologyOpenDiskGap center radiusOut point gapOut ∧
          Cont point gapOut radiusOut := by
  intro disk extraCarrier radiusStep gapStep
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have radiusOutCarrier : UnaryHistory radiusOut :=
                    unary_cont_closed radiusCarrier extraCarrier radiusStep
                  have gapOutCarrier : UnaryHistory gapOut :=
                    unary_cont_closed gapCarrier extraCarrier gapStep
                  have pointGapOut : Cont point gapOut radiusOut := by
                    cases pointGap
                    cases gapStep
                    cases radiusStep
                    exact append_assoc point gap extra
                  exact And.intro
                    (And.intro centerCarrier
                      (And.intro radiusOutCarrier
                        (And.intro pointCarrier
                          (And.intro gapOutCarrier pointGapOut))))
                    pointGapOut

end BEDC.Derived.ComplexTopologyUp

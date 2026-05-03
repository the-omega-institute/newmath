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

theorem ComplexTopologyOpenDiskGap_gap_deterministic
    {center radius point gap gap' : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> Cont point gap' radius ->
      hsame gap gap' := by
  intro disk alternativeGap
  exact cont_left_cancel disk.right.right.right.right alternativeGap

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

theorem ComplexTopologyOpenDisk_gap_modulus {z0 r z : BHist} :
    OpenDisk z0 r z ->
      (∃ gap : BHist, UnaryHistory gap ∧ Cont gap z r) ∧
        (hsame r BHist.Empty -> False) := by
  intro disk
  cases disk with
  | intro _centerCarrier diskRest =>
      cases diskRest with
      | intro _radiusUnary diskRest =>
          cases diskRest with
          | intro pointCarrier gapWitness =>
              exact And.intro gapWitness
                (fun radiusEmpty =>
                  match gapWitness with
                  | Exists.intro gap gapData =>
                      have emptyGapPoint : Cont gap z BHist.Empty :=
                        cont_result_hsame_transport gapData.right radiusEmpty
                      have endpoints := cont_empty_result_inversion emptyGapPoint
                      have pointEmpty : hsame z BHist.Empty := by
                        cases endpoints.right
                        exact hsame_refl BHist.Empty
                      ComplexHistoryCarrier_not_empty pointCarrier pointEmpty)

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

theorem ComplexTopologyOpenDiskGap_radius_not_empty {center radius point gap : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> hsame radius BHist.Empty -> False := by
  intro disk sameRadius
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro _gapCarrier pointGap =>
                  have emptyParts :=
                    cont_empty_result_inversion (cont_result_hsame_transport pointGap sameRadius)
                  exact ComplexHistoryCarrier_not_empty pointCarrier emptyParts.left

theorem ComplexTopologyOpenDiskGap_empty_gap_radius_point {center radius point gap : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> hsame gap BHist.Empty ->
      hsame radius point := by
  intro disk sameGap
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro _pointCarrier rest =>
              cases rest with
              | intro _gapCarrier pointGap =>
                  exact (cont_right_unit_iff.mp
                    (cont_hsame_transport (hsame_refl point) sameGap
                      (hsame_refl radius) pointGap))

theorem ComplexTopologyOpenDiskGap_unary_suffix_transport
    {center radius point gap q pointq radiusq : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> UnaryHistory q -> Cont point q pointq ->
      Cont radius q radiusq ->
        ComplexTopologyOpenDiskGap center radiusq pointq gap ∧ Cont pointq gap radiusq := by
  intro disk suffixCarrier pointSuffix radiusSuffix
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have shiftedPointCarrier : ComplexHistoryCarrier pointq :=
                    BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport pointSuffix.symm
                      (ComplexHistoryCarrier_append_unary_closed pointCarrier suffixCarrier)
                  have shiftedRadiusCarrier : UnaryHistory radiusq :=
                    unary_cont_closed radiusCarrier suffixCarrier radiusSuffix
                  have shiftedBoundary : Cont pointq gap radiusq := by
                    apply cont_intro
                    exact
                      radiusSuffix.trans
                        ((congrArg (fun h => append h q) pointGap).trans
                          ((append_assoc point gap q).trans
                            ((congrArg (append point)
                              (unary_append_comm gapCarrier suffixCarrier)).trans
                              ((append_assoc point q gap).symm.trans
                                (congrArg (fun h => append h gap) pointSuffix.symm)))))
                  exact
                    And.intro
                      (And.intro centerCarrier
                        (And.intro shiftedRadiusCarrier
                          (And.intro shiftedPointCarrier
                            (And.intro gapCarrier shiftedBoundary))))
                      shiftedBoundary

theorem ComplexTopologyOpenDiskGap_center_point_unary_suffix_transport
    {center radius point gap q centerq pointq radiusq : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap -> UnaryHistory q ->
      Cont center q centerq -> Cont point q pointq -> Cont radius q radiusq ->
        ComplexTopologyOpenDiskGap centerq radiusq pointq gap ∧ Cont pointq gap radiusq := by
  intro disk suffixCarrier centerSuffix pointSuffix radiusSuffix
  cases disk with
  | intro centerCarrier rest =>
      have shiftedCenterCarrier : ComplexHistoryCarrier centerq :=
        BEDC.Derived.ProdUp.ProdHistoryCarrier_hsame_transport centerSuffix.symm
          (ComplexHistoryCarrier_append_unary_closed centerCarrier suffixCarrier)
      have shifted :=
        ComplexTopologyOpenDiskGap_unary_suffix_transport
          (And.intro centerCarrier rest) suffixCarrier pointSuffix radiusSuffix
      cases shifted with
      | intro shiftedDisk shiftedBoundary =>
          exact And.intro
            (And.intro shiftedCenterCarrier
              (And.intro shiftedDisk.right.left
                (And.intro shiftedDisk.right.right.left
                  (And.intro shiftedDisk.right.right.right.left shiftedBoundary))))
            shiftedBoundary

end BEDC.Derived.ComplexTopologyUp

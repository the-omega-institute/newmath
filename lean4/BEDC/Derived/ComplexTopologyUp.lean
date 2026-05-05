import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Derived.ComplexUp
import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.HolomorphicUp

def ComplexTopologyOpenDiskGap (center radius point gap : BHist) : Prop :=
  ComplexHistoryCarrier center ∧ UnaryHistory radius ∧ ComplexHistoryCarrier point ∧
    UnaryHistory gap ∧ Cont point gap radius

def ComplexTopologyClosedDiskGap (center radius point gap : BHist) : Prop :=
  ComplexHistoryCarrier center ∧ UnaryHistory radius ∧ ComplexHistoryCarrier point ∧
    UnaryHistory gap ∧ (Cont point gap radius ∨ hsame point radius)

def ComplexTopologyOpenSet (U : BHist -> Prop) : Prop :=
  forall {z : BHist}, U z ->
    exists center radius gap : BHist,
      ComplexTopologyOpenDiskGap center radius z gap ∧ Cont z gap radius

def ComplexTopologyDyadicNet (K : BHist -> Prop) (precision : BHist)
    (net : List BHist) : Prop :=
  UnaryHistory precision ∧
    forall z : BHist, K z ->
      exists center gap : BHist, List.Mem center net ∧
        ComplexTopologyOpenDiskGap center precision z gap

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

theorem ComplexTopologyClosedDiskGap_hsame_transport
    {center center' radius radius' point point' gap gap' : BHist} :
    ComplexTopologyClosedDiskGap center radius point gap ->
      ComplexHistoryClassifier center center' -> hsame radius radius' ->
        ComplexHistoryClassifier point point' -> hsame gap gap' ->
          ComplexTopologyClosedDiskGap center' radius' point' gap' ∧
            (Cont point' gap' radius' ∨ hsame point' radius') := by
  intro disk centerClass sameRadius pointClass sameGap
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro _pointCarrier rest =>
              cases rest with
              | intro gapCarrier boundary =>
                  cases centerClass with
                  | intro _centerSource centerRest =>
                      cases centerRest with
                      | intro centerTarget _sameCenter =>
                          cases pointClass with
                          | intro _pointSource pointRest =>
                              cases pointRest with
                              | intro pointTarget samePoint =>
                                  have radiusCarrier' : UnaryHistory radius' :=
                                    unary_transport radiusCarrier sameRadius
                                  have gapCarrier' : UnaryHistory gap' :=
                                    unary_transport gapCarrier sameGap
                                  have boundary' :
                                      Cont point' gap' radius' ∨ hsame point' radius' := by
                                    cases boundary with
                                    | inl pointGap =>
                                        exact Or.inl
                                          (cont_hsame_transport samePoint sameGap sameRadius
                                            pointGap)
                                    | inr pointRadius =>
                                        exact Or.inr
                                          (hsame_trans (hsame_symm samePoint)
                                            (hsame_trans pointRadius sameRadius))
                                  exact And.intro
                                    (And.intro centerTarget
                                      (And.intro radiusCarrier'
                                        (And.intro pointTarget
                                          (And.intro gapCarrier' boundary'))))
                                    boundary'

theorem ComplexTopologyOpenSet_union_closed {I : Type} {U : I -> BHist -> Prop} :
    (forall i : I, ComplexTopologyOpenSet (U i)) ->
      ComplexTopologyOpenSet (fun z : BHist => exists i : I, U i z) := by
  intro branchOpen _z unionMember
  cases unionMember with
  | intro i member =>
      exact branchOpen i member

theorem ComplexTopologyOpenSet_intersection_witness_closed {U V : BHist -> Prop} :
    ComplexTopologyOpenSet U -> ComplexTopologyOpenSet V ->
      ComplexTopologyOpenSet (fun z : BHist => U z ∧ V z) ∧
        forall {z : BHist}, U z ∧ V z ->
          exists centerU radiusU gapU centerV radiusV gapV : BHist,
            ComplexTopologyOpenDiskGap centerU radiusU z gapU ∧ Cont z gapU radiusU ∧
              ComplexTopologyOpenDiskGap centerV radiusV z gapV ∧ Cont z gapV radiusV := by
  intro openU openV
  constructor
  · intro z member
    exact openU member.left
  · intro z member
    cases openU member.left with
    | intro centerU leftRest =>
        cases leftRest with
        | intro radiusU leftRest =>
            cases leftRest with
            | intro gapU leftWitness =>
                cases openV member.right with
                | intro centerV rightRest =>
                    cases rightRest with
                    | intro radiusV rightRest =>
                        cases rightRest with
                        | intro gapV rightWitness =>
                            exact Exists.intro centerU
                              (Exists.intro radiusU
                                (Exists.intro gapU
                                  (Exists.intro centerV
                                    (Exists.intro radiusV
                                      (Exists.intro gapV
                                        (And.intro leftWitness.left
                                          (And.intro leftWitness.right
                                            (And.intro rightWitness.left
                                              rightWitness.right))))))))

theorem ComplexTopologyOpenSet_intersection_witnesses {U V : BHist -> Prop} :
    ComplexTopologyOpenSet U -> ComplexTopologyOpenSet V ->
      ComplexTopologyOpenSet (fun z : BHist => U z ∧ V z) ∧
        (forall {z : BHist}, U z ∧ V z ->
          (exists center radius gap : BHist,
            ComplexTopologyOpenDiskGap center radius z gap ∧ Cont z gap radius) ∧
          (exists center radius gap : BHist,
            ComplexTopologyOpenDiskGap center radius z gap ∧ Cont z gap radius)) := by
  intro openU openV
  constructor
  · intro z both
    exact openU both.left
  · intro z both
    exact And.intro (openU both.left) (openV both.right)

theorem ComplexTopologyClosedDiskGap_strict_radius_not_empty
    {center radius point gap : BHist} :
    ComplexTopologyClosedDiskGap center radius point gap -> Cont point gap radius ->
      hsame radius BHist.Empty -> False := by
  intro disk strictBoundary radiusEmpty
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro pointCarrier _rest =>
              have emptyBoundary :
                  Cont point gap BHist.Empty :=
                cont_result_hsame_transport strictBoundary radiusEmpty
              have emptyParts := cont_empty_result_inversion emptyBoundary
              exact ComplexHistoryCarrier_not_empty pointCarrier emptyParts.left

theorem ComplexTopologyClosedDiskGap_radius_not_empty {center radius point gap : BHist} :
    ComplexTopologyClosedDiskGap center radius point gap -> hsame radius BHist.Empty -> False := by
  intro disk radiusEmpty
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro _gapCarrier boundary =>
                  cases boundary with
                  | inl pointGap =>
                      have emptyBoundary : Cont point gap BHist.Empty :=
                        cont_result_hsame_transport pointGap radiusEmpty
                      have emptyParts := cont_empty_result_inversion emptyBoundary
                      exact ComplexHistoryCarrier_not_empty pointCarrier emptyParts.left
                  | inr pointRadius =>
                      exact ComplexHistoryCarrier_not_empty pointCarrier
                        (hsame_trans pointRadius radiusEmpty)

theorem ComplexTopologyClosedDiskGap_empty_gap_radius_point {center radius point gap : BHist} :
    ComplexTopologyClosedDiskGap center radius point gap -> hsame gap BHist.Empty ->
      hsame radius point := by
  intro disk sameGap
  cases disk with
  | intro _centerCarrier rest =>
      cases rest with
      | intro _radiusCarrier rest =>
          cases rest with
          | intro _pointCarrier rest =>
              cases rest with
              | intro _gapCarrier boundary =>
                  cases boundary with
                  | inl pointGap =>
                      exact cont_right_unit_iff.mp
                        (cont_hsame_transport (hsame_refl point) sameGap
                          (hsame_refl radius) pointGap)
                  | inr pointRadius =>
                      exact hsame_symm pointRadius

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

theorem ComplexTopologyOpenSet_intersection_radius_witnesses_nonempty
    {U V : BHist -> Prop} {z : BHist} :
    ComplexTopologyOpenSet U -> ComplexTopologyOpenSet V -> U z -> V z ->
      exists cU rU gU cV rV gV : BHist,
        ComplexTopologyOpenDiskGap cU rU z gU ∧ Cont z gU rU ∧
          (hsame rU BHist.Empty -> False) ∧
            ComplexTopologyOpenDiskGap cV rV z gV ∧ Cont z gV rV ∧
              (hsame rV BHist.Empty -> False) := by
  intro openU openV memberU memberV
  cases openU memberU with
  | intro cU witnessU =>
      cases witnessU with
      | intro rU witnessU =>
          cases witnessU with
          | intro gU witnessU =>
              cases witnessU with
              | intro diskU boundaryU =>
                  cases openV memberV with
                  | intro cV witnessV =>
                      cases witnessV with
                      | intro rV witnessV =>
                          cases witnessV with
                          | intro gV witnessV =>
                              cases witnessV with
                              | intro diskV boundaryV =>
                                  exact
                                    Exists.intro cU
                                      (Exists.intro rU
                                        (Exists.intro gU
                                          (Exists.intro cV
                                            (Exists.intro rV
                                              (Exists.intro gV
                                                (And.intro diskU
                                                  (And.intro boundaryU
                                                    (And.intro
                                                      (ComplexTopologyOpenDiskGap_radius_not_empty
                                                        diskU)
                                                      (And.intro diskV
                                                        (And.intro boundaryV
                                                          (ComplexTopologyOpenDiskGap_radius_not_empty
                                                            diskV)))))))))))

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

theorem ComplexTopologyOpenDiskGap_empty_gap_radius_point_iff
    {center radius point gap : BHist} :
    ComplexTopologyOpenDiskGap center radius point gap ->
      (hsame gap BHist.Empty ↔ hsame radius point) := by
  intro disk
  constructor
  · intro sameGap
    exact ComplexTopologyOpenDiskGap_empty_gap_radius_point disk sameGap
  · intro sameRadius
    cases disk with
    | intro _centerCarrier rest =>
        cases rest with
        | intro _radiusCarrier rest =>
            cases rest with
            | intro _pointCarrier rest =>
                cases rest with
                | intro _gapCarrier pointGap =>
                    have pointGapPoint : Cont point gap point :=
                      cont_result_hsame_transport pointGap sameRadius
                    exact cont_left_cancel pointGapPoint (cont_right_unit point)

theorem ComplexTopologyOpenDiskGap_visible_radius_gap_cases
    {center radiusTail point gap : BHist} :
    ComplexTopologyOpenDiskGap center (BHist.e1 radiusTail) point gap ->
      (gap = BHist.Empty ∧ hsame point (BHist.e1 radiusTail)) ∨
        (∃ gapTail : BHist,
          gap = BHist.e1 gapTail ∧
            ComplexTopologyOpenDiskGap center radiusTail point gapTail) := by
  intro disk
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier pointGap =>
                  have resultCases := cont_e1_result_inversion pointGap
                  cases resultCases with
                  | inl visible =>
                      exact Or.inl visible
                  | inr descended =>
                      cases descended with
                      | intro gapTail tailData =>
                          cases tailData with
                          | intro gapEq tailRel =>
                              have radiusTailCarrier : UnaryHistory radiusTail :=
                                unary_e1_inversion radiusCarrier
                              have gapTailCarrier : UnaryHistory gapTail := by
                                cases gapEq
                                exact unary_e1_inversion gapCarrier
                              exact Or.inr
                                (Exists.intro gapTail
                                  (And.intro gapEq
                                    (And.intro centerCarrier
                                      (And.intro radiusTailCarrier
                                        (And.intro pointCarrier
                                          (And.intro gapTailCarrier tailRel))))))

theorem ComplexTopologyClosedDiskGap_visible_radius_boundary_cases
    {center radiusTail point gap : BHist} :
    ComplexTopologyClosedDiskGap center (BHist.e1 radiusTail) point gap ->
      ((gap = BHist.Empty ∧ hsame point (BHist.e1 radiusTail)) ∨
          (∃ gapTail : BHist,
            gap = BHist.e1 gapTail ∧
              ComplexTopologyClosedDiskGap center radiusTail point gapTail)) ∨
        hsame point (BHist.e1 radiusTail) := by
  intro disk
  cases disk with
  | intro centerCarrier rest =>
      cases rest with
      | intro radiusCarrier rest =>
          cases rest with
          | intro pointCarrier rest =>
              cases rest with
              | intro gapCarrier boundary =>
                  cases boundary with
                  | inl pointGap =>
                      have resultCases := cont_e1_result_inversion pointGap
                      cases resultCases with
                      | inl visible =>
                          exact Or.inl (Or.inl visible)
                      | inr descended =>
                          cases descended with
                          | intro gapTail tailData =>
                              cases tailData with
                              | intro gapEq tailRel =>
                                  have radiusTailCarrier : UnaryHistory radiusTail :=
                                    unary_e1_inversion radiusCarrier
                                  have gapTailCarrier : UnaryHistory gapTail := by
                                    cases gapEq
                                    exact unary_e1_inversion gapCarrier
                                  exact Or.inl
                                    (Or.inr
                                      (Exists.intro gapTail
                                        (And.intro gapEq
                                          (And.intro centerCarrier
                                            (And.intro radiusTailCarrier
                                              (And.intro pointCarrier
                                                (And.intro gapTailCarrier
                                                  (Or.inl tailRel))))))))
                  | inr pointRadius =>
                      exact Or.inr pointRadius

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

theorem ComplexTopologyOpenDiskGap_semanticNameCert {center radius point gap : BHist}
    (witness : ComplexTopologyOpenDiskGap center radius point gap) :
    SemanticNameCert (fun g : BHist => ComplexTopologyOpenDiskGap center radius point g)
      (fun g : BHist => ComplexTopologyOpenDiskGap center radius point g)
      (fun g : BHist => ComplexTopologyOpenDiskGap center radius point g) hsame := by
  constructor
  · constructor
    · exact Exists.intro gap witness
    · intro g _carrier
      exact hsame_refl g
    · intro g g' same
      exact hsame_symm same
    · intro g g' g'' sameGG' sameG'G''
      exact hsame_trans sameGG' sameG'G''
    · intro g g' same carrier
      have centerClass : ComplexHistoryClassifier center center :=
        And.intro carrier.left (And.intro carrier.left (hsame_refl center))
      have pointClass : ComplexHistoryClassifier point point :=
        And.intro carrier.right.right.left
          (And.intro carrier.right.right.left (hsame_refl point))
      exact
        (ComplexTopologyOpenDiskGap_hsame_transport carrier centerClass
          (hsame_refl radius) pointClass same).left
  · intro g source
    exact source
  · intro g source
    exact source

end BEDC.Derived.ComplexTopologyUp

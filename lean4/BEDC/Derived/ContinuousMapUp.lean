import BEDC.Derived.ContinuousUp
import BEDC.Derived.ContinuousUp.EmptyMap
import BEDC.Derived.ContinuousUp.GraphModulusReadback
import BEDC.Derived.MetricUp
import BEDC.Derived.MetricUp.Transport
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

def ContinuousMapCarrier (source map target modulus cert distance : BHist) : Prop :=
  ContinuousFunctionCarrier source map target modulus cert ∧
    MetricDistanceWitness source target distance

theorem ContinuousMapCarrier_canonical_distance_iff {source map target modulus cert : BHist} :
    ContinuousMapCarrier source map target modulus cert (append source target) ↔
      ContinuousFunctionCarrier source map target modulus cert := by
  constructor
  · intro carrier
    exact carrier.left
  · intro carrier
    cases carrier with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro modulusCarrier rest =>
                    cases rest with
                    | intro sourceMap targetCert =>
                        exact
                          And.intro
                            (And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro mapCarrier
                                  (And.intro modulusCarrier
                                    (And.intro sourceMap targetCert)))))
                            (And.intro sourceCarrier
                              (And.intro targetCarrier
                                (And.intro (unary_append_closed sourceCarrier targetCarrier)
                                  (cont_intro rfl))))

theorem ContinuousMapCarrier_empty_distance_exact {source map modulus cert : BHist} :
    ContinuousMapCarrier source map BHist.Empty modulus cert BHist.Empty ↔
      UnaryHistory source ∧ UnaryHistory map ∧ UnaryHistory modulus ∧
        hsame source BHist.Empty ∧ hsame map BHist.Empty ∧ hsame cert modulus := by
  constructor
  · intro carrier
    have functionCarrier := carrier.left
    have distanceEndpoints :=
      (MetricDistanceWitness_empty_distance_iff (x := source) (y := BHist.Empty)).mp
        carrier.right
    have graphEndpoints :=
      cont_empty_result_inversion functionCarrier.right.right.right.right.left
    exact
      And.intro functionCarrier.left
        (And.intro functionCarrier.right.right.left
          (And.intro functionCarrier.right.right.right.left
            (And.intro distanceEndpoints.left
              (And.intro graphEndpoints.right
                (cont_left_unit_result functionCarrier.right.right.right.right.right)))))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro mapCarrier rest =>
            cases rest with
            | intro modulusCarrier rest =>
                cases rest with
                | intro sourceEmpty rest =>
                    cases rest with
                    | intro mapEmpty certModulus =>
                        have graphRel : Cont source map BHist.Empty := by
                          cases sourceEmpty
                          cases mapEmpty
                          exact cont_right_unit BHist.Empty
                        have certRel : Cont BHist.Empty modulus cert :=
                          cont_left_unit_iff.mpr certModulus
                        exact
                          And.intro
                            (And.intro sourceCarrier
                              (And.intro unary_empty
                                (And.intro mapCarrier
                                  (And.intro modulusCarrier (And.intro graphRel certRel)))))
                            ((MetricDistanceWitness_empty_distance_iff
                              (x := source) (y := BHist.Empty)).mpr
                              (And.intro sourceEmpty (hsame_refl BHist.Empty)))

theorem ContinuousMapCarrier_empty_cert_iff {source map target modulus dist : BHist} :
    ContinuousMapCarrier source map target modulus BHist.Empty dist ↔
      hsame source BHist.Empty ∧ hsame map BHist.Empty ∧
        hsame target BHist.Empty ∧ hsame modulus BHist.Empty ∧ hsame dist BHist.Empty := by
  constructor
  · intro carrier
    have functionData :=
      (ContinuousFunctionCarrier_empty_cert_iff
        (source := source) (map := map) (target := target) (modulus := modulus)).mp
        carrier.left
    have sourceEmpty : hsame source BHist.Empty := functionData.left
    have targetEmpty : hsame target BHist.Empty := functionData.right.right.left
    have distEmpty : hsame dist BHist.Empty := by
      cases sourceEmpty
      cases targetEmpty
      exact cont_deterministic carrier.right.right.right.right (cont_right_unit BHist.Empty)
    exact
      And.intro functionData.left
        (And.intro functionData.right.left
          (And.intro functionData.right.right.left
            (And.intro functionData.right.right.right distEmpty)))
  · intro endpoints
    cases endpoints.left
    cases endpoints.right.left
    cases endpoints.right.right.left
    cases endpoints.right.right.right.left
    cases endpoints.right.right.right.right
    exact
      And.intro
        ((ContinuousFunctionCarrier_empty_cert_iff
          (source := BHist.Empty) (map := BHist.Empty) (target := BHist.Empty)
          (modulus := BHist.Empty)).mpr
          (And.intro (hsame_refl BHist.Empty)
            (And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))))
        ((MetricDistanceWitness_empty_distance_iff
          (x := BHist.Empty) (y := BHist.Empty)).mpr
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))

theorem ContinuousMap_empty_map_empty_distance_iff {source modulus cert : BHist} :
    (ContinuousFunctionCarrier source BHist.Empty source modulus cert ∧
      MetricDistanceWitness source source BHist.Empty) ↔
      ContinuousModulusWitness source modulus cert ∧ hsame source BHist.Empty := by
  constructor
  · intro data
    cases data with
    | intro carrier distance =>
        cases carrier with
        | intro sourceCarrier rest =>
            cases rest with
            | intro _targetCarrier rest =>
                cases rest with
                | intro _mapCarrier rest =>
                    cases rest with
                    | intro modulusCarrier rest =>
                        cases rest with
                        | intro _graph certRel =>
                            have endpoints :=
                              (MetricDistanceWitness_empty_distance_iff
                                (x := source) (y := source)).mp distance
                            exact
                              And.intro
                                (And.intro sourceCarrier
                                  (And.intro modulusCarrier
                                    (And.intro
                                      (unary_cont_closed sourceCarrier modulusCarrier certRel)
                                      certRel)))
                                endpoints.left
  · intro data
    cases data with
    | intro modulusWitness sourceEmpty =>
        exact
          And.intro
            (ContinuousFunctionCarrier_empty_map_identity modulusWitness)
            ((MetricDistanceWitness_empty_distance_iff
              (x := source) (y := source)).mpr (And.intro sourceEmpty sourceEmpty))

theorem ContinuousMap_empty_identity_metric_witness_reflects
    {x y x' y' d mx my cx cy : BHist} :
    ContinuousFunctionCarrier x BHist.Empty x' mx cx ->
      ContinuousFunctionCarrier y BHist.Empty y' my cy ->
        MetricDistanceWitness x' y' d -> MetricDistanceWitness x y d := by
  intro left right imageWitness
  have sameX : hsame x' x :=
    (ContinuousFunctionCarrier_empty_map_iff.mp left).left
  have sameY : hsame y' y :=
    (ContinuousFunctionCarrier_empty_map_iff.mp right).left
  exact
    And.intro (unary_transport imageWitness.left sameX)
      (And.intro (unary_transport imageWitness.right.left sameY)
        (And.intro imageWitness.right.right.left
          (cont_hsame_transport sameX sameY (hsame_refl d) imageWitness.right.right.right)))

theorem ContinuousMap_empty_identity_metric_result_deterministic
    {x y x' y' d d' mx my cx cy : BHist} :
    ContinuousFunctionCarrier x BHist.Empty x' mx cx ->
      ContinuousFunctionCarrier y BHist.Empty y' my cy ->
        MetricDistanceWitness x' y' d -> MetricDistanceWitness x y d' -> hsame d d' := by
  intro left right imageWitness sourceWitness
  have reflected :
      MetricDistanceWitness x y d :=
    ContinuousMap_empty_identity_metric_witness_reflects left right imageWitness
  exact
    MetricDistanceWitness_hsame_result_deterministic
      (hsame_refl x) (hsame_refl y) reflected sourceWitness

theorem ContinuousMap_empty_target_metric_rebased_carrier
    {source modulus cert dist cert' : BHist} :
    ContinuousFunctionCarrier source BHist.Empty source modulus cert ->
      MetricDistanceWitness source BHist.Empty dist ->
        Cont dist modulus cert' ->
          ContinuousFunctionCarrier dist BHist.Empty dist modulus cert' := by
  intro carrier distance certRel
  exact
    And.intro distance.right.right.left
      (And.intro distance.right.right.left
        (And.intro unary_empty
          (And.intro carrier.right.right.right.left
            (And.intro (cont_right_unit dist) certRel))))

theorem ContinuousMap_empty_target_metric_cert_deterministic
    {source modulus cert dist cert' : BHist} :
    ContinuousFunctionCarrier source BHist.Empty source modulus cert ->
      MetricDistanceWitness source BHist.Empty dist ->
        Cont dist modulus cert' -> hsame cert cert' := by
  intro carrier distance certRel
  have distData := Iff.mp MetricDistanceWitness_empty_right_iff distance
  exact
    cont_respects_hsame (hsame_symm distData.right) (hsame_refl modulus)
      carrier.right.right.right.right.right certRel

theorem ContinuousMapCarrier_target_cert_distance_deterministic
    {source map target target' modulus cert cert' distance distance' : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousMapCarrier source map target' modulus cert' distance' ->
        hsame target target' ∧ hsame cert cert' ∧ hsame distance distance' ∧
          Cont source target distance := by
  intro left right
  have targetCertSame :
      hsame target target' ∧ hsame cert cert' :=
    ContinuousFunctionCarrier_target_cert_deterministic left.left right.left
  have distanceSame : hsame distance distance' :=
    MetricDistanceWitness_hsame_result_deterministic
      (hsame_refl source) targetCertSame.left left.right right.right
  exact And.intro targetCertSame.left
    (And.intro targetCertSame.right
      (And.intro distanceSame left.right.right.right.right))

theorem ContinuousMapCarrier_empty_map_empty_distance_boundaries_iff
    {source target modulus cert : BHist} :
    ContinuousMapCarrier source BHist.Empty target modulus cert BHist.Empty ↔
      hsame source BHist.Empty ∧ hsame target BHist.Empty ∧
        ContinuousModulusWitness BHist.Empty modulus cert := by
  constructor
  · intro carrier
    have mapData :=
      (ContinuousFunctionCarrier_empty_map_iff
        (source := source) (target := target) (modulus := modulus) (cert := cert)).mp
        carrier.left
    have distanceData :=
      (MetricDistanceWitness_empty_distance_iff (x := source) (y := target)).mp
        carrier.right
    cases distanceData.right
    exact And.intro distanceData.left (And.intro (hsame_refl BHist.Empty) mapData.right)
  · intro data
    cases data.left
    cases data.right.left
    have functionCarrier :
        ContinuousFunctionCarrier BHist.Empty BHist.Empty BHist.Empty modulus cert :=
      (ContinuousFunctionCarrier_empty_map_iff
        (source := BHist.Empty) (target := BHist.Empty) (modulus := modulus) (cert := cert)).mpr
        (And.intro (hsame_refl BHist.Empty) data.right.right)
    have distanceWitness : MetricDistanceWitness BHist.Empty BHist.Empty BHist.Empty :=
      (MetricDistanceWitness_empty_distance_iff (x := BHist.Empty) (y := BHist.Empty)).mpr
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    exact And.intro functionCarrier distanceWitness

theorem ContinuousMapCarrier_prefix_canonical_distance_closed
    {p source map target modulus cert distance : BHist} :
    UnaryHistory p -> ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousMapCarrier (append p source) map (append p target) modulus (append p cert)
        (append (append p source) (append p target)) := by
  intro prefixCarrier carrier
  have functionCarrier :
      ContinuousFunctionCarrier (append p source) map (append p target) modulus
        (append p cert) :=
    ContinuousFunctionCarrier_prefix_closed prefixCarrier carrier.left
  cases carrier with
  | intro baseFunction _distanceWitness =>
      cases baseFunction with
      | intro sourceCarrier rest =>
          cases rest with
          | intro targetCarrier _functionRest =>
              exact
                And.intro functionCarrier
                  (And.intro (unary_append_closed prefixCarrier sourceCarrier)
                    (And.intro (unary_append_closed prefixCarrier targetCarrier)
                      (And.intro
                        (unary_append_closed
                          (unary_append_closed prefixCarrier sourceCarrier)
                          (unary_append_closed prefixCarrier targetCarrier))
                        (cont_intro rfl))))

theorem ContinuousMapFunctionCarrier_metric_graph_exactness
    {source map target modulus cert dist : BHist} :
    ContinuousFunctionCarrier source map target modulus cert ->
      MetricDistanceWitness source map dist -> Cont source map target ∧ hsame dist target := by
  intro functionCarrier metricWitness
  have readback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback functionCarrier
  exact And.intro readback.left (cont_deterministic metricWitness.right.right.right readback.left)

theorem ContinuousMap_comp_graph_depth_add
    {source mid target mapF mapG mapFG modF modG modFG certF certG certFG : BHist} :
    ContinuousFunctionCarrier source mapF mid modF certF ->
      ContinuousFunctionCarrier mid mapG target modG certG -> Cont mapF mapG mapFG ->
        Cont modF modG modFG -> Cont target modFG certFG ->
          MetricDistanceDepth target = MetricDistanceDepth source + MetricDistanceDepth mapFG := by
  intro first second graphRel modulusRel certRel
  have compositeCarrier :
      ContinuousFunctionCarrier source mapFG target modFG certFG :=
    ContinuousFunctionCarrier_comp_closed first second graphRel modulusRel certRel
  have graphWitness : MetricDistanceWitness source mapFG target := by
    cases compositeCarrier with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro _modulusCarrier rest =>
                    cases rest with
                    | intro graph _cert =>
                        exact
                          And.intro sourceCarrier
                            (And.intro mapCarrier (And.intro targetCarrier graph))
  exact MetricDistanceWitness_depth_add graphWitness

end BEDC.Derived.ContinuousMapUp

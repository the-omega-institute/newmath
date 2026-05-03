import BEDC.Derived.ContinuousUp
import BEDC.Derived.ContinuousUp.EmptyMap
import BEDC.Derived.MetricUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

def ContinuousMapCarrier (source map target modulus cert dist : BHist) : Prop :=
  ContinuousFunctionCarrier source map target modulus cert ∧
    MetricDistanceWitness source target dist

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

end BEDC.Derived.ContinuousMapUp

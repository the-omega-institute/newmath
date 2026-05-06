import BEDC.Derived.ContinuousMapUp.CategoryMetricDecomposition

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_composition_category_metric_package
    {source mid target mapF mapG mapFG modF modG modFG certF certG certFG distF distG
      displayed : BHist} :
    ContinuousMapCarrier source mapF mid modF certF distF ->
      ContinuousMapCarrier mid mapG target modG certG distG ->
        Cont mapF mapG mapFG ->
          Cont modF modG modFG ->
            Cont target modFG certFG ->
              ContinuousMapCarrier source mapFG target modFG certFG (append source target) ∧
                CategoryHomCarrier source target mapFG ∧
                  ContinuousModulusWitness target modFG certFG ∧
                    MetricDistanceWitness source target (append source target) ∧
                      (ContinuousMapCarrier source mapFG target modFG certFG displayed ->
                        hsame displayed (append source target)) := by
  intro first second graphRel modulusRel certRel
  have canonical :
      ContinuousMapCarrier source mapFG target modFG certFG (append source target) :=
    ContinuousMapCarrier_comp_closed first second graphRel modulusRel certRel
  have decomposed :=
    (ContinuousMapCarrier_category_metric_decomposition (source := source) (map := mapFG)
      (target := target) (modulus := modFG) (cert := certFG)
      (distance := append source target)).mp canonical
  exact And.intro canonical
    (And.intro decomposed.left
      (And.intro decomposed.right.left
        (And.intro decomposed.right.right.left
          (fun displayedCarrier =>
            hsame_symm
              (ContinuousMapCarrier_target_cert_distance_deterministic canonical
                displayedCarrier).right.right.left))))

theorem ContinuousMapCarrier_composition_canonical_certificate_package
    {source mid target mapF mapG mapFG modF modG modFG certF certG certFG distF distG
      displayed : BHist} :
    ContinuousMapCarrier source mapF mid modF certF distF ->
      ContinuousMapCarrier mid mapG target modG certG distG ->
        Cont mapF mapG mapFG ->
          Cont modF modG modFG ->
            Cont target modFG certFG ->
              ContinuousMapCarrier source mapFG target modFG certFG (append source target) ∧
                (ContinuousMapCarrier source mapFG target modFG certFG displayed ->
                  hsame displayed (append source target)) ∧
                  MetricDistanceDepth target =
                    MetricDistanceDepth source + MetricDistanceDepth mapFG := by
  intro first second graphRel modulusRel certRel
  have canonical :
      ContinuousMapCarrier source mapFG target modFG certFG (append source target) :=
    ContinuousMapCarrier_comp_closed first second graphRel modulusRel certRel
  have graphWitness : MetricDistanceWitness source mapFG target :=
    And.intro canonical.left.left
      (And.intro canonical.left.right.right.left
        (And.intro canonical.left.right.left canonical.left.right.right.right.right.left))
  exact And.intro canonical
    (And.intro
      (fun displayedCarrier =>
        hsame_symm
          (ContinuousMapCarrier_target_cert_distance_deterministic canonical
            displayedCarrier).right.right.left)
      (MetricDistanceWitness_depth_add graphWitness))

end BEDC.Derived.ContinuousMapUp

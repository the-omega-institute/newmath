import BEDC.Derived.ContinuousUp
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

end BEDC.Derived.ContinuousMapUp

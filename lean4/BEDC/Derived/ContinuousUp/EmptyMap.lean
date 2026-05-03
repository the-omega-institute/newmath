import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_empty_map_iff {source target modulus cert : BHist} :
    ContinuousFunctionCarrier source BHist.Empty target modulus cert ↔
      hsame target source ∧ ContinuousModulusWitness target modulus cert := by
  constructor
  · intro carrier
    cases carrier with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro _mapCarrier rest =>
                cases rest with
                | intro modulusCarrier rest =>
                    cases rest with
                    | intro sourceMap targetCert =>
                        exact
                          And.intro (cont_right_unit_iff.mp sourceMap)
                            (And.intro targetCarrier
                              (And.intro modulusCarrier
                                (And.intro
                                  (unary_cont_closed targetCarrier modulusCarrier targetCert)
                                  targetCert)))
  · intro data
    cases data with
    | intro sameTarget witness =>
        cases witness with
        | intro targetCarrier rest =>
            cases rest with
            | intro modulusCarrier rest =>
                cases rest with
                | intro _certCarrier targetCert =>
                    exact
                      And.intro (unary_transport targetCarrier sameTarget)
                        (And.intro targetCarrier
                          (And.intro unary_empty
                            (And.intro modulusCarrier
                              (And.intro (cont_right_unit_iff.mpr sameTarget) targetCert))))

theorem ContinuousFunctionCarrier_empty_cert_iff {source map target modulus : BHist} :
    ContinuousFunctionCarrier source map target modulus BHist.Empty ↔
      hsame source BHist.Empty ∧ hsame map BHist.Empty ∧
        hsame target BHist.Empty ∧ hsame modulus BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro _targetCarrier rest =>
            cases rest with
            | intro _mapCarrier rest =>
                cases rest with
                | intro _modulusCarrier rest =>
                    cases rest with
                    | intro sourceMap targetCert =>
                        have certParts := cont_empty_result_inversion targetCert
                        have graphParts : source = BHist.Empty ∧ map = BHist.Empty := by
                          cases certParts.left
                          exact cont_empty_result_inversion sourceMap
                        exact And.intro graphParts.left
                          (And.intro graphParts.right
                            (And.intro certParts.left certParts.right))
  · intro endpoints
    cases endpoints.left
    cases endpoints.right.left
    cases endpoints.right.right.left
    cases endpoints.right.right.right
    exact And.intro unary_empty
      (And.intro unary_empty
        (And.intro unary_empty
          (And.intro unary_empty
            (And.intro (cont_right_unit BHist.Empty) (cont_right_unit BHist.Empty)))))

end BEDC.Derived.ContinuousUp

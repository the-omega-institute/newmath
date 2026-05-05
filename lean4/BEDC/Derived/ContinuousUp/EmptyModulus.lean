import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_empty_modulus_iff {source target : BHist} :
    ContinuousModulusWitness source BHist.Empty target <->
      UnaryHistory source ∧ UnaryHistory target ∧ hsame source target := by
  constructor
  · intro witness
    cases witness with
    | intro sourceCarrier rest =>
        cases rest with
        | intro _emptyCarrier rest =>
            cases rest with
            | intro targetCarrier sourceEmpty =>
                exact
                  And.intro sourceCarrier
                    (And.intro targetCarrier (hsame_symm (Iff.mp cont_right_unit_iff sourceEmpty)))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier sameSourceTarget =>
            exact
              And.intro sourceCarrier
                (And.intro unary_empty
                  (And.intro targetCarrier
                    (Iff.mpr cont_right_unit_iff (hsame_symm sameSourceTarget))))

theorem ContinuousFunctionCarrier_empty_modulus_iff {source map target cert : BHist} :
    ContinuousFunctionCarrier source map target BHist.Empty cert ↔
      UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory map ∧
        Cont source map target ∧ hsame cert target := by
  constructor
  · intro carrier
    cases carrier with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro _emptyCarrier rest =>
                    cases rest with
                    | intro sourceMap targetCert =>
                        exact
                          And.intro sourceCarrier
                            (And.intro targetCarrier
                              (And.intro mapCarrier
                                (And.intro sourceMap (Iff.mp cont_right_unit_iff targetCert))))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro sourceMap sameCertTarget =>
                    exact
                      And.intro sourceCarrier
                        (And.intro targetCarrier
                          (And.intro mapCarrier
                            (And.intro unary_empty
                              (And.intro sourceMap
                                (Iff.mpr cont_right_unit_iff sameCertTarget)))))

end BEDC.Derived.ContinuousUp

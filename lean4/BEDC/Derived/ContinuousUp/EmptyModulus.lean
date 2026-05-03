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

end BEDC.Derived.ContinuousUp

import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_empty_source_iff {modulus target : BHist} :
    ContinuousModulusWitness BHist.Empty modulus target ↔
      UnaryHistory target ∧ hsame modulus target := by
  constructor
  · intro witness
    cases witness with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro _modulusCarrier rest =>
            cases rest with
            | intro targetCarrier modulusRel =>
                exact
                  And.intro targetCarrier
                    (hsame_symm (cont_left_unit_result modulusRel))
  · intro data
    cases data with
    | intro targetCarrier sameModulus =>
        exact
          And.intro unary_empty
            (And.intro
              (unary_transport targetCarrier (hsame_symm sameModulus))
              (And.intro targetCarrier
                (Iff.mpr cont_left_unit_iff (hsame_symm sameModulus))))

end BEDC.Derived.ContinuousUp

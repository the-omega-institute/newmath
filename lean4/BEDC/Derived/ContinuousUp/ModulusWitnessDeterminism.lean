import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousModulusWitness_modulus_hsame_deterministic
    {source source' modulus modulus' target target' : BHist} :
    hsame source source' → hsame target target' →
      ContinuousModulusWitness source modulus target →
        ContinuousModulusWitness source' modulus' target' → hsame modulus modulus' := by
  intro sameSource sameTarget left right
  cases sameSource
  cases sameTarget
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _modulusCarrier leftRest =>
          cases leftRest with
          | intro _targetCarrier leftRel =>
              cases right with
              | intro _sourceCarrier' rightRest =>
                  cases rightRest with
                  | intro _modulusCarrier' rightRest =>
                      cases rightRest with
                      | intro _targetCarrier' rightRel =>
                          exact cont_left_cancel leftRel rightRel

end BEDC.Derived.ContinuousUp

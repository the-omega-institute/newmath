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

theorem ContinuousModulusChain_second_deterministic
    {source first second second' target : BHist} :
    ContinuousModulusChain source first second target →
      ContinuousModulusChain source first second' target → hsame second second' := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _firstCarrier leftRest =>
          cases leftRest with
          | intro _secondCarrier leftRest =>
              cases leftRest with
              | intro _targetCarrier leftWitness =>
                  cases leftWitness with
                  | intro middle leftMiddle =>
                      cases leftMiddle with
                      | intro firstRel secondRel =>
                          cases right with
                          | intro _sourceCarrier' rightRest =>
                              cases rightRest with
                              | intro _firstCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _secondCarrier' rightRest =>
                                      cases rightRest with
                                      | intro _targetCarrier' rightWitness =>
                                          cases rightWitness with
                                          | intro middle' rightMiddle =>
                                              cases rightMiddle with
                                              | intro firstRel' secondRel' =>
                                                  have sameMiddle : hsame middle middle' :=
                                                    cont_deterministic firstRel firstRel'
                                                  cases sameMiddle
                                                  exact cont_left_cancel secondRel secondRel'

theorem ContinuousFunctionCarrier_map_deterministic
    {source map map' target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert →
      ContinuousFunctionCarrier source map' target modulus cert → hsame map map' := by
  intro left right
  cases left with
  | intro _sourceCarrier leftRest =>
      cases leftRest with
      | intro _targetCarrier leftRest =>
          cases leftRest with
          | intro _mapCarrier leftRest =>
              cases leftRest with
              | intro _modulusCarrier leftRest =>
                  cases leftRest with
                  | intro sourceMap _targetCert =>
                      cases right with
                      | intro _sourceCarrier' rightRest =>
                          cases rightRest with
                          | intro _targetCarrier' rightRest =>
                              cases rightRest with
                              | intro _mapCarrier' rightRest =>
                                  cases rightRest with
                                  | intro _modulusCarrier' rightRest =>
                                      cases rightRest with
                                      | intro sourceMap' _targetCert' =>
                                          exact cont_left_cancel sourceMap sourceMap'

end BEDC.Derived.ContinuousUp

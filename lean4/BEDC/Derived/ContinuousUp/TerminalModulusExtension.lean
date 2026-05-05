import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_terminal_modulus_extension
    {source map target modulus cert extra modulus' cert' : BHist} :
    ContinuousFunctionCarrier source map target modulus cert ->
      ContinuousModulusWitness cert extra cert' -> Cont modulus extra modulus' ->
        ContinuousFunctionCarrier source map target modulus' cert' := by
  intro carrier extraWitness modulusRel
  cases carrier with
  | intro sourceCarrier carrierRest =>
      cases carrierRest with
      | intro targetCarrier carrierRest =>
          cases carrierRest with
          | intro mapCarrier carrierRest =>
              cases carrierRest with
              | intro modulusCarrier carrierRest =>
                  cases carrierRest with
                  | intro sourceMap targetModulus =>
                      cases extraWitness with
                      | intro certCarrier extraRest =>
                          cases extraRest with
                          | intro extraCarrier extraRest =>
                              cases extraRest with
                              | intro cert'Carrier certExtra =>
                                  have chain :
                                      ContinuousModulusChain target modulus extra cert' :=
                                    And.intro targetCarrier
                                      (And.intro modulusCarrier
                                        (And.intro extraCarrier
                                          (And.intro cert'Carrier
                                            (Exists.intro cert
                                              (And.intro targetModulus certExtra)))))
                                  have replacementWitness :
                                      ContinuousModulusWitness target modulus' cert' :=
                                    ContinuousModulusChain_composite_closed chain modulusRel
                                  cases replacementWitness with
                                  | intro _targetCarrier witnessRest =>
                                      cases witnessRest with
                                      | intro modulus'Carrier witnessRest =>
                                          exact
                                            And.intro sourceCarrier
                                              (And.intro targetCarrier
                                                (And.intro mapCarrier
                                                  (And.intro modulus'Carrier
                                                    (And.intro sourceMap
                                                      witnessRest.right))))

end BEDC.Derived.ContinuousUp

import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_terminal_modulus_extension
    {source map target modulus cert extra modulus' cert' : BHist} :
    ContinuousFunctionCarrier source map target modulus cert ->
      ContinuousModulusWitness cert extra cert' ->
        Cont modulus extra modulus' ->
          ContinuousFunctionCarrier source map target modulus' cert' := by
  intro carrier terminalWitness modulusRel
  have baseCarrier := carrier
  cases carrier with
  | intro _sourceCarrier carrierRest =>
      cases carrierRest with
      | intro targetCarrier carrierRest =>
          cases carrierRest with
          | intro _mapCarrier carrierRest =>
              cases carrierRest with
              | intro modulusCarrier carrierRest =>
                  cases carrierRest with
                  | intro _sourceMap targetModulus =>
                      cases terminalWitness with
                      | intro certCarrier witnessRest =>
                          cases witnessRest with
                          | intro extraCarrier witnessRest =>
                              cases witnessRest with
                              | intro cert'Carrier certExtra =>
                                  have chain :
                                      ContinuousModulusChain target modulus extra cert' :=
                                    And.intro targetCarrier
                                      (And.intro modulusCarrier
                                        (And.intro extraCarrier
                                          (And.intro cert'Carrier
                                            (Exists.intro cert
                                              (And.intro targetModulus certExtra)))))
                                  exact
                                    ContinuousFunctionCarrier_modulus_chain_replacement baseCarrier chain
                                      modulusRel

end BEDC.Derived.ContinuousUp

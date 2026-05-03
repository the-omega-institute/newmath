import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_graph_modulus_cont_readback
    {source map target modulus cert : BHist} :
    ContinuousFunctionCarrier source map target modulus cert ->
      Cont source map target ∧ Cont target modulus cert ∧
        ContinuousModulusWitness source map target ∧
          ContinuousModulusWitness target modulus cert := by
  intro carrier
  cases carrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro targetCarrier rest =>
          cases rest with
          | intro mapCarrier rest =>
              cases rest with
              | intro modulusCarrier rest =>
                  cases rest with
                  | intro graphRel modulusRel =>
                      have certCarrier : UnaryHistory cert :=
                        unary_cont_closed targetCarrier modulusCarrier modulusRel
                      exact
                        And.intro graphRel
                          (And.intro modulusRel
                            (And.intro
                              (And.intro sourceCarrier
                                (And.intro mapCarrier
                                  (And.intro targetCarrier graphRel)))
                              (And.intro targetCarrier
                                (And.intro modulusCarrier
                                  (And.intro certCarrier modulusRel)))))

end BEDC.Derived.ContinuousUp

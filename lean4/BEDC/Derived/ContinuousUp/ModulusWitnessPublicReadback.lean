import BEDC.Derived.ContinuousUp.ModulusWitnessDeterminism

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_composite_public_readback
    {source first second middle target composite : BHist} :
    ContinuousModulusWitness source first middle ->
      ContinuousModulusWitness middle second target -> Cont first second composite ->
        ContinuousModulusWitness source composite target ∧
          (forall {target' : BHist}, ContinuousModulusWitness source composite target' ->
            hsame target target') := by
  intro firstWitness secondWitness compositeRel
  cases firstWitness with
  | intro sourceCarrier firstRest =>
      cases firstRest with
      | intro firstCarrier firstRest =>
          cases firstRest with
          | intro middleCarrier firstRel =>
              cases secondWitness with
              | intro _middleCarrier secondRest =>
                  cases secondRest with
                  | intro secondCarrier secondRest =>
                      cases secondRest with
                      | intro targetCarrier secondRel =>
                          have chain : ContinuousModulusChain source first second target :=
                            And.intro sourceCarrier
                              (And.intro firstCarrier
                                (And.intro secondCarrier
                                  (And.intro targetCarrier
                                    (Exists.intro middle (And.intro firstRel secondRel)))))
                          have compositeWitness :
                              ContinuousModulusWitness source composite target :=
                            ContinuousModulusChain_composite_closed chain compositeRel
                          constructor
                          · exact compositeWitness
                          · intro target' displayed
                            exact
                              ContinuousModulusWitness_target_hsame_deterministic
                                (hsame_refl source) compositeWitness displayed

end BEDC.Derived.ContinuousUp

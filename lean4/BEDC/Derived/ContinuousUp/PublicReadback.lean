import BEDC.Derived.ContinuousUp.ModulusWitnessPublicReadback

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousModulusChain_composite_public_readback
    {source first second target composite : BHist} :
    ContinuousModulusChain source first second target -> Cont first second composite ->
      ContinuousModulusWitness source composite target ∧
        (forall {target' : BHist}, ContinuousModulusWitness source composite target' ->
          hsame target target') := by
  intro chain compositeRel
  have factorized := ContinuousModulusChain_factorizes chain
  cases factorized with
  | intro middle legs =>
      exact
        ContinuousModulusWitness_composite_public_readback
          legs.left legs.right compositeRel

end BEDC.Derived.ContinuousUp

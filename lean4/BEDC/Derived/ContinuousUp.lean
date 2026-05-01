import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ContinuousModulusWitness (source modulus target : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory target ∧ Cont source modulus target

def ContinuousModulusChain (source first second target : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory first ∧ UnaryHistory second ∧ UnaryHistory target ∧
    ∃ middle : BHist, Cont source first middle ∧ Cont middle second target

theorem ContinuousModulusChain_composite_closed {source first second target composite : BHist} :
    ContinuousModulusChain source first second target -> Cont first second composite ->
      ContinuousModulusWitness source composite target := by
  intro chain compositeRel
  cases chain with
  | intro sourceCarrier rest =>
      cases rest with
      | intro firstCarrier rest =>
          cases rest with
          | intro secondCarrier rest =>
              cases rest with
              | intro targetCarrier chainWitness =>
                  cases chainWitness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          cases firstRel
                          cases secondRel
                          cases compositeRel
                          exact
                            And.intro sourceCarrier
                              (And.intro
                                (unary_cont_closed firstCarrier secondCarrier (cont_intro rfl))
                                (And.intro targetCarrier
                                  (cont_intro (append_assoc source first second))))

end BEDC.Derived.ContinuousUp

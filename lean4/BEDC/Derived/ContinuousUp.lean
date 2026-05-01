import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

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

def ContinuousFunctionCarrier (source map target modulus cert : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory map ∧ UnaryHistory modulus ∧
    Cont source map target ∧ Cont target modulus cert

theorem ContinuousFunctionCarrier_comp_closed
    {source middle target f g fg modF modG modFG certF certG cert : BHist} :
    ContinuousFunctionCarrier source f middle modF certF ->
      ContinuousFunctionCarrier middle g target modG certG ->
        Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
          ContinuousFunctionCarrier source fg target modFG cert := by
  intro first second fgRel modRel certRel
  cases first with
  | intro sourceCarrier firstRest =>
      cases firstRest with
      | intro _middleCarrier firstRest =>
          cases firstRest with
          | intro fCarrier firstRest =>
              cases firstRest with
              | intro modFCarrier firstRest =>
                  cases firstRest with
                  | intro sourceMap _certFRel =>
                      cases second with
                      | intro _middleCarrier' secondRest =>
                          cases secondRest with
                          | intro targetCarrier secondRest =>
                              cases secondRest with
                              | intro gCarrier secondRest =>
                                  cases secondRest with
                                  | intro modGCarrier secondRest =>
                                      cases secondRest with
                                      | intro middleMap _certGRel =>
                                          have fgCarrier : UnaryHistory fg :=
                                            unary_cont_closed fCarrier gCarrier fgRel
                                          have modFGCarrier : UnaryHistory modFG :=
                                            unary_cont_closed modFCarrier modGCarrier modRel
                                          have sourceTarget : Cont source fg target := by
                                            cases sourceMap
                                            cases middleMap
                                            cases fgRel
                                            exact cont_intro (append_assoc source f g)
                                          exact
                                            And.intro sourceCarrier
                                              (And.intro targetCarrier
                                                (And.intro fgCarrier
                                                  (And.intro modFGCarrier
                                                    (And.intro sourceTarget certRel))))

theorem ContinuousModulusChain_prefix_closed {p source first second target : BHist} :
    UnaryHistory p -> ContinuousModulusChain source first second target ->
      ContinuousModulusChain (append p source) first second (append p target) := by
  intro prefixCarrier chain
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
                          exact
                            And.intro (unary_append_closed prefixCarrier sourceCarrier)
                              (And.intro firstCarrier
                                (And.intro secondCarrier
                                  (And.intro (unary_append_closed prefixCarrier targetCarrier)
                                    (Exists.intro (append p middle)
                                      (And.intro
                                        (cont_intro
                                          ((congrArg (append p) firstRel).trans
                                            (append_assoc p source first).symm))
                                        (cont_intro
                                          ((congrArg (append p) secondRel).trans
                                            (append_assoc p middle second).symm)))))))

end BEDC.Derived.ContinuousUp

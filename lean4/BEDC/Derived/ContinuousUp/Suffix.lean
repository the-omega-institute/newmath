import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_suffix_iff {p source modulus target : BHist} :
    ContinuousModulusWitness source (append modulus p) (append target p) <->
      UnaryHistory p /\ ContinuousModulusWitness source modulus target := by
  constructor
  · intro suffixed
    cases suffixed with
    | intro sourceCarrier rest =>
        cases rest with
        | intro suffixedModulusCarrier rest =>
            cases rest with
            | intro suffixedTargetCarrier rel =>
                have pCarrier : UnaryHistory p := unary_append_right_factor suffixedModulusCarrier
                have modulusCarrier : UnaryHistory modulus :=
                  unary_append_left_factor suffixedModulusCarrier
                have targetCarrier : UnaryHistory target :=
                  unary_append_left_factor suffixedTargetCarrier
                have baseRel : Cont source modulus target := by
                  apply cont_intro
                  apply append_right_cancel (k := p)
                  exact rel.trans (append_assoc source modulus p).symm
                exact
                  And.intro pCarrier
                    (And.intro sourceCarrier
                      (And.intro modulusCarrier (And.intro targetCarrier baseRel)))
  · intro base
    cases base with
    | intro pCarrier witness =>
        cases witness with
        | intro sourceCarrier rest =>
            cases rest with
            | intro modulusCarrier rest =>
                cases rest with
                | intro targetCarrier rel =>
                    exact
                      And.intro sourceCarrier
                        (And.intro (unary_append_closed modulusCarrier pCarrier)
                          (And.intro (unary_append_closed targetCarrier pCarrier)
                            (cont_intro
                              ((congrArg (fun result => append result p) rel).trans
                                (append_assoc source modulus p)))))

theorem ContinuousModulusChain_suffix_iff {p source first second target : BHist} :
    ContinuousModulusChain source first (append second p) (append target p) <->
      UnaryHistory p /\ ContinuousModulusChain source first second target := by
  constructor
  · intro suffixed
    cases suffixed with
    | intro sourceCarrier rest =>
        cases rest with
        | intro firstCarrier rest =>
            cases rest with
            | intro suffixedSecondCarrier rest =>
                cases rest with
                | intro suffixedTargetCarrier chainWitness =>
                    cases chainWitness with
                    | intro middle middleData =>
                        cases middleData with
                        | intro firstRel secondRel =>
                            have middleCarrier : UnaryHistory middle :=
                              unary_cont_closed sourceCarrier firstCarrier firstRel
                            have suffixedSecondWitness :
                                ContinuousModulusWitness middle (append second p)
                                  (append target p) :=
                              And.intro middleCarrier
                                (And.intro suffixedSecondCarrier
                                  (And.intro suffixedTargetCarrier secondRel))
                            have suffixData :=
                              (ContinuousModulusWitness_suffix_iff (p := p) (source := middle)
                                (modulus := second) (target := target)).mp suffixedSecondWitness
                            cases suffixData with
                            | intro pCarrier secondWitness =>
                                cases secondWitness with
                                | intro _middleCarrier rest =>
                                    cases rest with
                                    | intro secondCarrier rest =>
                                        cases rest with
                                        | intro targetCarrier baseSecondRel =>
                                            exact
                                              And.intro pCarrier
                                                (And.intro sourceCarrier
                                                  (And.intro firstCarrier
                                                    (And.intro secondCarrier
                                                      (And.intro targetCarrier
                                                        (Exists.intro middle
                                                          (And.intro firstRel
                                                            baseSecondRel))))))
  · intro base
    cases base with
    | intro pCarrier chain =>
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
                                have middleCarrier : UnaryHistory middle :=
                                  unary_cont_closed sourceCarrier firstCarrier firstRel
                                have secondWitness :
                                    ContinuousModulusWitness middle second target :=
                                  And.intro middleCarrier
                                    (And.intro secondCarrier
                                      (And.intro targetCarrier secondRel))
                                have suffixedSecondWitness :=
                                  (ContinuousModulusWitness_suffix_iff (p := p)
                                    (source := middle) (modulus := second) (target := target)).mpr
                                    (And.intro pCarrier secondWitness)
                                cases suffixedSecondWitness with
                                | intro _middleCarrier rest =>
                                    cases rest with
                                    | intro suffixedSecondCarrier rest =>
                                        cases rest with
                                        | intro suffixedTargetCarrier suffixedSecondRel =>
                                            exact
                                              And.intro sourceCarrier
                                                (And.intro firstCarrier
                                                  (And.intro suffixedSecondCarrier
                                                    (And.intro suffixedTargetCarrier
                                                      (Exists.intro middle
                                                        (And.intro firstRel
                                                          suffixedSecondRel)))))

end BEDC.Derived.ContinuousUp

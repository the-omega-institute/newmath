import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusChain_empty_moduli_iff {source target : BHist} :
    ContinuousModulusChain source BHist.Empty BHist.Empty target ↔
      UnaryHistory source ∧ UnaryHistory target ∧ hsame target source := by
  constructor
  · intro chain
    cases chain with
    | intro sourceCarrier rest =>
        cases rest with
        | intro _firstCarrier rest =>
            cases rest with
            | intro _secondCarrier rest =>
                cases rest with
                | intro targetCarrier chainWitness =>
                    cases chainWitness with
                    | intro middle middleData =>
                        cases middleData with
                        | intro firstRel secondRel =>
                            have sameMiddleSource : hsame middle source :=
                              Iff.mp cont_right_unit_iff firstRel
                            have sameTargetMiddle : hsame target middle :=
                              Iff.mp cont_right_unit_iff secondRel
                            exact And.intro sourceCarrier
                              (And.intro targetCarrier
                                (hsame_trans sameTargetMiddle sameMiddleSource))
  · intro data
    cases data with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier sameTargetSource =>
            exact
              And.intro sourceCarrier
                (And.intro unary_empty
                  (And.intro unary_empty
                    (And.intro targetCarrier
                      (Exists.intro source
                        (And.intro (cont_right_unit source)
                          (Iff.mpr cont_right_unit_iff sameTargetSource))))))

end BEDC.Derived.ContinuousUp

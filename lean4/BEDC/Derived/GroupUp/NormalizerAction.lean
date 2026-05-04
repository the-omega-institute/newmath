import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonNormalizerAction_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      let Conj : BHist -> BHist -> BHist := fun t y => append (append t y) BHist.Empty
      GroupSingletonCarrier (Conj s x) ∧ GroupSingletonCarrier (Conj BHist.Empty x) ∧
        GroupSingletonClassifier (Conj s x) x ∧
          GroupSingletonClassifier (Conj BHist.Empty (Conj s x)) x := by
  intro carrierS carrierX
  cases carrierS
  cases carrierX
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      · exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

end BEDC.Derived.GroupUp

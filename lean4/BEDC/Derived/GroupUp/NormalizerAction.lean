import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingleton_normalizer_action_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      let Conj := fun u y : BHist => append (append u y) BHist.Empty
      GroupSingletonCarrier (Conj s x) ∧
        GroupSingletonCarrier (Conj BHist.Empty x) ∧
          GroupSingletonClassifier (Conj s x) x ∧
            GroupSingletonClassifier (Conj BHist.Empty (Conj s x)) x := by
  intro carrierS carrierX
  cases carrierS
  cases carrierX
  dsimp
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact And.intro rfl (And.intro rfl rfl)
      · exact And.intro rfl (And.intro rfl rfl)

end BEDC.Derived.GroupUp

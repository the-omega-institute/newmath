import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_suffix_product_unit_split_iff {L R p q : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonClassifier (append (append p q) L) (append BHist.Empty R) <->
        GroupSingletonCarrier p ∧ GroupSingletonCarrier q) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have outerSplit := append_eq_empty_iff.mp classified.left
    exact append_eq_empty_iff.mp outerSplit.left
  · intro split
    have productCarrier : GroupSingletonCarrier (append p q) :=
      append_eq_empty_iff.mpr split
    have leftCarrier : GroupSingletonCarrier (append (append p q) L) :=
      append_eq_empty_iff.mpr (And.intro productCarrier carrierL)
    have rightCarrier : GroupSingletonCarrier (append BHist.Empty R) :=
      append_eq_empty_iff.mpr (And.intro (hsame_refl BHist.Empty) carrierR)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.GroupUp

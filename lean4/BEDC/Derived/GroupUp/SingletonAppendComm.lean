import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_append_comm_congr {h h2 k k2 : BHist} :
    GroupSingletonClassifier (append h k) (append h2 k2) ->
      GroupSingletonClassifier (append k h) (append k2 h2) := by
  intro classified
  have leftParts := append_eq_empty_iff.mp classified.left
  have rightParts := append_eq_empty_iff.mp classified.right.left
  have leftCarrier : GroupSingletonCarrier (append k h) :=
    append_eq_empty_iff.mpr (And.intro leftParts.right leftParts.left)
  have rightCarrier : GroupSingletonCarrier (append k2 h2) :=
    append_eq_empty_iff.mpr (And.intro rightParts.right rightParts.left)
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.GroupUp

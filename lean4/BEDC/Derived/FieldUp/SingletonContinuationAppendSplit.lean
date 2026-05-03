import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_append_split_iff {L P Q R T : BHist} :
    Cont P Q T ->
      (FieldSingletonClassifier (append L T) R <->
        FieldSingletonCarrier L /\ FieldSingletonCarrier P /\ FieldSingletonCarrier Q /\
          FieldSingletonCarrier R) := by
  intro continuation
  constructor
  · intro classified
    have appendEmpty := append_eq_empty_iff.mp classified.left
    have emptyContinuation : Cont P Q BHist.Empty :=
      cont_result_hsame_transport continuation appendEmpty.right
    have endpoints := cont_empty_result_inversion emptyContinuation
    exact And.intro appendEmpty.left
      (And.intro endpoints.left (And.intro endpoints.right classified.right.left))
  · intro carriers
    have carrierT : FieldSingletonCarrier T :=
      hsame_trans continuation
        (append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right.left))
    have leftCarrier : FieldSingletonCarrier (append L T) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carrierT)
    exact And.intro leftCarrier
      (And.intro carriers.right.right.right
        (hsame_trans leftCarrier (hsame_symm carriers.right.right.right)))

end BEDC.Derived.FieldUp

import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_continuation_comm_iff {P Q L R : BHist} :
    Cont P Q L -> Cont Q P R ->
      (FieldSingletonClassifier L R ↔ FieldSingletonClassifier P Q) := by
  intro leftRel rightRel
  constructor
  · intro classifiedLR
    have leftEmpty : hsame L BHist.Empty := classifiedLR.left
    have emptyLeftRel : Cont P Q BHist.Empty :=
      cont_result_hsame_transport leftRel leftEmpty
    have inputParts := cont_empty_result_inversion emptyLeftRel
    exact And.intro inputParts.left
      (And.intro inputParts.right
        (hsame_trans inputParts.left (hsame_symm inputParts.right)))
  · intro classifiedPQ
    have leftCarrier : FieldSingletonCarrier L :=
      cont_respects_hsame classifiedPQ.left classifiedPQ.right.left leftRel
        (cont_left_unit BHist.Empty)
    have rightCarrier : FieldSingletonCarrier R :=
      cont_respects_hsame classifiedPQ.right.left classifiedPQ.left rightRel
        (cont_left_unit BHist.Empty)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.FieldUp

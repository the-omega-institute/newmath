import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeqUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def SeqRootSource (PointCarrier : BHist -> Prop) (s : BHist -> BHist) : Prop :=
  forall {n : BHist}, UnaryHistory n -> PointCarrier (s n)

def SeqPointwiseClassifier (PointCarrier : BHist -> Prop)
    (PointClassifier : BHist -> BHist -> Prop) (s t : BHist -> BHist) : Prop :=
  forall {n : BHist}, UnaryHistory n ->
    PointCarrier (s n) ∧ PointCarrier (t n) ∧ PointClassifier (s n) (t n)

theorem SeqPointwiseClassifier_rows {PointCarrier : BHist -> Prop}
    {PointClassifier : BHist -> BHist -> Prop} (cert : NameCert PointCarrier PointClassifier)
    {s t u : BHist -> BHist} :
    SeqRootSource PointCarrier s -> SeqRootSource PointCarrier t ->
      SeqRootSource PointCarrier u ->
        SeqPointwiseClassifier PointCarrier PointClassifier s s ∧
          (SeqPointwiseClassifier PointCarrier PointClassifier s t ->
            SeqPointwiseClassifier PointCarrier PointClassifier t s) ∧
          (SeqPointwiseClassifier PointCarrier PointClassifier s t ->
            SeqPointwiseClassifier PointCarrier PointClassifier t u ->
              SeqPointwiseClassifier PointCarrier PointClassifier s u) := by
  intro sourceS sourceT sourceU
  constructor
  · intro n unaryN
    have carrierS : PointCarrier (s n) := sourceS unaryN
    exact And.intro carrierS (And.intro carrierS (NameCert.equiv_refl cert carrierS))
  · constructor
    · intro sameST n unaryN
      have row := sameST unaryN
      exact And.intro row.right.left
        (And.intro row.left (NameCert.equiv_symm cert row.right.right))
    · intro sameST sameTU n unaryN
      have rowST := sameST unaryN
      have rowTU := sameTU unaryN
      exact And.intro rowST.left
        (And.intro rowTU.right.left
          (NameCert.equiv_trans cert rowST.right.right rowTU.right.right))

end BEDC.Derived.SeqUp

import BEDC.FKernel.NameCert

namespace BEDC.Derived.HashUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def HashSecondPreimageSuccess
    (HashEval : BHist -> BHist -> Prop)
    (MsgClassifier DigClassifier : BHist -> BHist -> Prop)
    (x x' : BHist) : Prop :=
  exists d : BHist, exists d' : BHist,
    HashEval x d ∧ HashEval x' d' ∧ (MsgClassifier x x' -> False) ∧
      DigClassifier d' d

def HashCollisionSuccess
    (HashEval : BHist -> BHist -> Prop)
    (MsgClassifier DigClassifier : BHist -> BHist -> Prop)
    (x x' : BHist) : Prop :=
  exists d : BHist, exists d' : BHist,
    HashEval x d ∧ HashEval x' d' ∧ (MsgClassifier x x' -> False) ∧
      DigClassifier d d'

theorem HashSecondPreimageSuccess_induces_collision
    {HashEval : BHist -> BHist -> Prop}
    {MsgCarrier DigCarrier : BHist -> Prop}
    {MsgClassifier DigClassifier : BHist -> BHist -> Prop}
    (digestCert : SemanticNameCert DigCarrier DigCarrier DigCarrier DigClassifier)
    {x x' : BHist} :
    HashSecondPreimageSuccess HashEval MsgClassifier DigClassifier x x' ->
      HashCollisionSuccess HashEval MsgClassifier DigClassifier x x' := by
  intro success
  cases success with
  | intro d successD =>
      cases successD with
      | intro d' transcript =>
          exact Exists.intro d
            (Exists.intro d'
              (And.intro transcript.left
                (And.intro transcript.right.left
                  (And.intro transcript.right.right.left
                    (digestCert.core.equiv_symm transcript.right.right.right)))))

end BEDC.Derived.HashUp

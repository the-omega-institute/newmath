import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont

namespace BEDC.Derived.HashUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont

def HashEvalTranscript (MsgCarrier DigCarrier : BHist -> Prop) (m d row : BHist) : Prop :=
  MsgCarrier m ∧ DigCarrier d ∧ Cont m d row

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

theorem HashCollisionSuccess_symmetric
    {HashEval : BHist -> BHist -> Prop}
    {MsgCarrier DigCarrier : BHist -> Prop}
    {MsgClassifier DigClassifier : BHist -> BHist -> Prop}
    (msgCert : SemanticNameCert MsgCarrier MsgCarrier MsgCarrier MsgClassifier)
    (digestCert : SemanticNameCert DigCarrier DigCarrier DigCarrier DigClassifier)
    {x x' : BHist} :
    HashCollisionSuccess HashEval MsgClassifier DigClassifier x x' ->
      HashCollisionSuccess HashEval MsgClassifier DigClassifier x' x := by
  intro success
  cases success with
  | intro d successD =>
      cases successD with
      | intro d' transcript =>
          have digestSymm : DigClassifier d' d :=
            digestCert.core.equiv_symm transcript.right.right.right
          have msgDistinct : MsgClassifier x' x -> False := by
            intro reversed
            exact transcript.right.right.left (msgCert.core.equiv_symm reversed)
          have notReverse : MsgClassifier x' x -> False := by
            intro reverse
            exact transcript.right.right.left (msgCert.core.equiv_symm reverse)
          exact Exists.intro d'
            (Exists.intro d
              (And.intro transcript.right.left
              (And.intro transcript.left
                (And.intro msgDistinct digestSymm))))

theorem HashCollisionTranscript_symmetric
    {HashEval : BHist -> BHist -> Prop}
    {MsgCarrier DigCarrier : BHist -> Prop}
    {MsgClassifier DigClassifier : BHist -> BHist -> Prop}
    (msgCert : SemanticNameCert MsgCarrier MsgCarrier MsgCarrier MsgClassifier)
    (digestCert : SemanticNameCert DigCarrier DigCarrier DigCarrier DigClassifier)
    {x x' d d' : BHist} :
    HashEval x d -> HashEval x' d' -> (MsgClassifier x x' -> False) ->
      DigClassifier d d' ->
      HashEval x' d' ∧ HashEval x d ∧ (MsgClassifier x' x -> False) ∧
        DigClassifier d' d := by
  intro evalLeft evalRight msgDistinct digestSame
  have msgDistinctSymm : MsgClassifier x' x -> False := by
    intro reversed
    exact msgDistinct (msgCert.core.equiv_symm reversed)
  exact And.intro evalRight
    (And.intro evalLeft
      (And.intro msgDistinctSymm (digestCert.core.equiv_symm digestSame)))

end BEDC.Derived.HashUp

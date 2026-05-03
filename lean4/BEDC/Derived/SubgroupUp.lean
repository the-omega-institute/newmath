import BEDC.Derived.GroupUp.Centralizer
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SubgroupCentralizerCarrier (mul : BHist -> BHist -> BHist) (a x : BHist) : Prop :=
  hsame (mul x a) (mul a x)

def SubgroupCentralizerClassifier (mul : BHist -> BHist -> BHist) (a x y : BHist) :
    Prop :=
  SubgroupCentralizerCarrier mul a x /\ SubgroupCentralizerCarrier mul a y /\
    hsame x y

def SubgroupCentralizerNormalizer (mul : BHist -> BHist -> BHist)
    (inv : BHist -> BHist) (a t : BHist) : Prop :=
  forall x : BHist, SubgroupCentralizerCarrier mul a x ->
    SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t))

theorem SubgroupCentralizer_semanticNameCert {mul : BHist -> BHist -> BHist}
    {a : BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) :
    SemanticNameCert (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
      (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerClassifier mul a) := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (BEDC.Derived.GroupUp.group_centralizer_empty_unit_mem leftId rightId)
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    · intro h k classified _carrierH
      exact classified.right.left
  · intro h source
    exact source
  · intro h source
    exact source

theorem SubgroupCentralizerCarrier_self_normalizes {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro centralT x centralX
  have centralizerMulClosed :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a v -> SubgroupCentralizerCarrier mul a (mul u v) := by
    intro u v centralU centralV
    have closedWithTail :=
      BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context
        assocC mulCongr centralU centralV
    exact hsame_trans (hsame_symm (rightId (mul (mul u v) a)))
      (hsame_trans closedWithTail (rightId (mul a (mul u v))))
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) :=
    BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralT
  have centralTX : SubgroupCentralizerCarrier mul a (mul t x) :=
    centralizerMulClosed centralT centralX
  exact centralizerMulClosed centralTX centralInvT

end BEDC.Derived.SubgroupUp

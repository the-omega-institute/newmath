import BEDC.Derived.GroupUp.Centralizer
import BEDC.Derived.GroupUp.CentralizerNormalizer
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SubgroupCentralizerCarrier (mul : BHist -> BHist -> BHist) (a x : BHist) : Prop :=
  hsame (mul x a) (mul a x)

def SubgroupCentralizerClassifier (mul : BHist -> BHist -> BHist) (a x y : BHist) : Prop :=
  SubgroupCentralizerCarrier mul a x ∧ SubgroupCentralizerCarrier mul a y ∧ hsame x y

def SubgroupCentralizerIntersectionCarrier
    (mul : BHist -> BHist -> BHist) (a b x : BHist) : Prop :=
  SubgroupCentralizerCarrier mul a x ∧ SubgroupCentralizerCarrier mul b x

def SubgroupCentralizerIntersectionClassifier
    (mul : BHist -> BHist -> BHist) (a b x y : BHist) : Prop :=
  SubgroupCentralizerIntersectionCarrier mul a b x ∧
    SubgroupCentralizerIntersectionCarrier mul a b y ∧ hsame x y

def SubgroupCentralizerNormalizer
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a t : BHist) : Prop :=
  forall x : BHist, SubgroupCentralizerCarrier mul a x ->
    SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t))

protected theorem SubgroupCentralizerCarrier_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y : BHist} :
    SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y ->
      SubgroupCentralizerCarrier mul a (mul x y) := by
  intro centralX centralY
  have closedEmpty :
      hsame (mul (mul (mul x y) a) BHist.Empty)
        (mul (mul a (mul x y)) BHist.Empty) := by
    exact BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context
      assocC mulCongr centralX centralY
  exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
    (hsame_trans closedEmpty (rightId (mul a (mul x y))))

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

protected theorem SubgroupCentralizer_certificate_target_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SemanticNameCert (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerClassifier mul a) ∧
      SubgroupCentralizerCarrier mul a BHist.Empty ∧
      (forall {x y : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y)) ∧
      (forall {x : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a (inv x)) ∧
      (forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> hsame x y ->
        SubgroupCentralizerCarrier mul a y) := by
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    BEDC.Derived.GroupUp.group_centralizer_empty_unit_mem leftId rightId
  have carrierTransport :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> hsame x y ->
        SubgroupCentralizerCarrier mul a y := by
    intro x y centralX sameXY
    exact hsame_trans (mulCongr (hsame_symm sameXY) (hsame_refl a))
      (hsame_trans centralX (mulCongr (hsame_refl a) sameXY))
  have mulClosed :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y) := by
    intro x y centralX centralY
    have closedWithUnit :
        hsame (mul (mul (mul x y) a) BHist.Empty)
          (mul (mul a (mul x y)) BHist.Empty) :=
      BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context assocC mulCongr
        centralX centralY
    exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
      (hsame_trans closedWithUnit (rightId (mul a (mul x y))))
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a (inv x) := by
    intro x centralX
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit assocC leftId
      rightId mulCongr leftInv rightInv centralX
  have semanticCert :
      SemanticNameCert (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerClassifier mul a) := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCentral
      equiv_refl := by
        intro h centralH
        exact And.intro centralH (And.intro centralH (hsame_refl h))
      equiv_symm := by
        intro h k sameHK
        exact And.intro sameHK.right.left
          (And.intro sameHK.left (hsame_symm sameHK.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k sameHK _centralH
        exact sameHK.right.left
    }
    pattern_sound := by
      intro h centralH
      exact centralH
    ledger_sound := by
      intro h centralH
      exact centralH
  }
  exact And.intro semanticCert
    (And.intro emptyCentral (And.intro mulClosed (And.intro invClosed carrierTransport)))

protected theorem SubgroupCentralizerIntersection_certificate_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    SemanticNameCert (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionClassifier mul a b) ∧
      SubgroupCentralizerIntersectionCarrier mul a b BHist.Empty ∧
      (forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        SubgroupCentralizerIntersectionCarrier mul a b y ->
          SubgroupCentralizerIntersectionCarrier mul a b (mul x y)) ∧
      (forall {x : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        SubgroupCentralizerIntersectionCarrier mul a b (inv x)) ∧
      (forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        hsame x y -> SubgroupCentralizerIntersectionCarrier mul a b y) := by
  have rowsA :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have rowsB :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := b)
  have emptyIntersection :
      SubgroupCentralizerIntersectionCarrier mul a b BHist.Empty :=
    And.intro rowsA.right.left rowsB.right.left
  have mulClosed :
      forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        SubgroupCentralizerIntersectionCarrier mul a b y ->
          SubgroupCentralizerIntersectionCarrier mul a b (mul x y) := by
    intro x y centralX centralY
    exact And.intro
      (rowsA.right.right.left centralX.left centralY.left)
      (rowsB.right.right.left centralX.right centralY.right)
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        SubgroupCentralizerIntersectionCarrier mul a b (inv x) := by
    intro x centralX
    exact And.intro
      (rowsA.right.right.right.left centralX.left)
      (rowsB.right.right.right.left centralX.right)
  have carrierTransport :
      forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x ->
        hsame x y -> SubgroupCentralizerIntersectionCarrier mul a b y := by
    intro x y centralX sameXY
    exact And.intro
      (rowsA.right.right.right.right centralX.left sameXY)
      (rowsB.right.right.right.right centralX.right sameXY)
  have semanticCert :
      SemanticNameCert (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionClassifier mul a b) := {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyIntersection
      equiv_refl := by
        intro h centralH
        exact And.intro centralH (And.intro centralH (hsame_refl h))
      equiv_symm := by
        intro h k sameHK
        exact And.intro sameHK.right.left
          (And.intro sameHK.left (hsame_symm sameHK.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k sameHK _centralH
        exact sameHK.right.left
    }
    pattern_sound := by
      intro h centralH
      exact centralH
    ledger_sound := by
      intro h centralH
      exact centralH
  }
  exact And.intro semanticCert
    (And.intro emptyIntersection (And.intro mulClosed (And.intro invClosed carrierTransport)))

protected theorem SubgroupCentralizer_self_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> forall {x : BHist},
      SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t)) := by
  intro centralT x centralX
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y) :=
    certificateRows.right.right.left
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerCarrier mul a x ->
        SubgroupCentralizerCarrier mul a (inv x) :=
    certificateRows.right.right.right.left
  have centralTX : SubgroupCentralizerCarrier mul a (mul t x) :=
    mulClosed centralT centralX
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) :=
    invClosed centralT
  exact mulClosed centralTX centralInvT

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
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) := by
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralT
  have centralTX : SubgroupCentralizerCarrier mul a (mul t x) := by
    exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralT centralX
  exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
    assocC rightId mulCongr centralTX centralInvT

protected theorem SubgroupCentralizerCarrier_self_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerNormalizer mul inv a t := by
  exact SubgroupCentralizerCarrier_self_normalizes
    assocC leftId rightId mulCongr leftInv rightInv

theorem SubgroupCentralizerNormalizer_kernel_classifier_refl
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerNormalizer mul inv a x ->
      SubgroupCentralizerNormalizer mul inv a x ∧
        SubgroupCentralizerNormalizer mul inv a x ∧
          SubgroupCentralizerCarrier mul a (mul (inv x) x) := by
  intro normalizes
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    certificateRows.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv x) x) :=
    carrierTransport emptyCentral (hsame_symm (leftInv x))
  exact And.intro normalizes (And.intro normalizes kernelCentral)

protected theorem SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t : BHist} :
    SubgroupCentralizerNormalizer mul inv a s ->
      SubgroupCentralizerNormalizer mul inv a t ->
        SubgroupCentralizerNormalizer mul inv a (mul s t) := by
  intro normalizesS normalizesT x centralX
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have composed :=
    BEDC.Derived.GroupUp.group_centralizer_normalizer_forward_action_composition_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv normalizesS normalizesT centralX
  exact carrierTransport composed.left (hsame_symm composed.right)

end BEDC.Derived.SubgroupUp

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
  SubgroupCentralizerIntersectionCarrier mul a b x ∧ SubgroupCentralizerIntersectionCarrier mul a b y ∧ hsame x y
def SubgroupCentralizerNormalizer
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a t : BHist) : Prop :=
  (forall x : BHist, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t))) ∧ (forall x : BHist, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (mul (mul (inv t) x) (inv (inv t))))
def SubgroupCentralizerQuotientKernel
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a x y : BHist) : Prop :=
  SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ SubgroupCentralizerCarrier mul a (mul (inv x) y)
def SubgroupCentralizerRightQuotientClassifier
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a x y : BHist) : Prop :=
  SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ Exists (fun z : BHist =>
        SubgroupCentralizerCarrier mul a z ∧ hsame y (mul x z))
def SubgroupCentralizerQuotientClassifier
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a x y : BHist) : Prop :=
  SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ Exists (fun c : BHist =>
        SubgroupCentralizerCarrier mul a c ∧ hsame (mul x c) y)
def SubgroupCentralizerRightCosetClassifier
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a x y : BHist) : Prop :=
  SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ ∃ z : BHist, SubgroupCentralizerCarrier mul a z ∧ hsame y (mul x z)
protected theorem SubgroupCentralizerCarrier_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    {a x y : BHist} :
    SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y) := by
  intro centralX centralY
  have closedEmpty :
      hsame (mul (mul (mul x y) a) BHist.Empty)
        (mul (mul a (mul x y)) BHist.Empty) := by
    exact BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context
      assocC mulCongr centralX centralY
  exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
    (hsame_trans closedEmpty (rightId (mul a (mul x y))))
protected theorem SubgroupCentralizerIntersectionCarrier_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    {a b x y : BHist} :
    SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b y -> SubgroupCentralizerIntersectionCarrier mul a b (mul x y) := by
  intro centralX centralY
  exact And.intro
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralX.left centralY.left)
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralX.right centralY.right)
protected theorem SubgroupCentralizerIntersectionCarrier_inv_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b x : BHist} :
    SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b (inv x) := by
  intro centralX
  exact And.intro
    (BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit assocC
      leftId rightId mulCongr leftInv rightInv centralX.left)
    (BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit assocC
      leftId rightId mulCongr leftInv rightInv centralX.right)
theorem SubgroupCentralizer_semanticNameCert {mul : BHist -> BHist -> BHist}
    {a : BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) :
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
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SemanticNameCert (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerClassifier mul a) ∧ SubgroupCentralizerCarrier mul a BHist.Empty ∧ (forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y)) ∧ (forall {x : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (inv x)) ∧ (forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> hsame x y -> SubgroupCentralizerCarrier mul a y) := by
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    BEDC.Derived.GroupUp.group_centralizer_empty_unit_mem leftId rightId
  have carrierTransport :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> hsame x y -> SubgroupCentralizerCarrier mul a y := by
    intro x y centralX sameXY
    exact hsame_trans (mulCongr (hsame_symm sameXY) (hsame_refl a))
      (hsame_trans centralX (mulCongr (hsame_refl a) sameXY))
  have mulClosed :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y) := by
    intro x y centralX centralY
    have closedWithUnit :
        hsame (mul (mul (mul x y) a) BHist.Empty)
          (mul (mul a (mul x y)) BHist.Empty) :=
      BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context assocC mulCongr
        centralX centralY
    exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
      (hsame_trans closedWithUnit (rightId (mul a (mul x y))))
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (inv x) := by
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
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    SemanticNameCert (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionCarrier mul a b)
        (SubgroupCentralizerIntersectionClassifier mul a b) ∧ SubgroupCentralizerIntersectionCarrier mul a b BHist.Empty ∧ (forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b y -> SubgroupCentralizerIntersectionCarrier mul a b (mul x y)) ∧ (forall {x : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b (inv x)) ∧ (forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> hsame x y -> SubgroupCentralizerIntersectionCarrier mul a b y) := by
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
      forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b y -> SubgroupCentralizerIntersectionCarrier mul a b (mul x y) := by
    intro x y centralX centralY
    exact And.intro
      (rowsA.right.right.left centralX.left centralY.left)
      (rowsB.right.right.left centralX.right centralY.right)
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> SubgroupCentralizerIntersectionCarrier mul a b (inv x) := by
    intro x centralX
    exact And.intro
      (rowsA.right.right.right.left centralX.left)
      (rowsB.right.right.right.left centralX.right)
  have carrierTransport :
      forall {x y : BHist}, SubgroupCentralizerIntersectionCarrier mul a b x -> hsame x y -> SubgroupCentralizerIntersectionCarrier mul a b y := by
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
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> forall {x : BHist},
      SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t)) := by
  intro centralT x centralX
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {x y : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y -> SubgroupCentralizerCarrier mul a (mul x y) :=
    certificateRows.right.right.left
  have invClosed :
      forall {x : BHist}, SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a (inv x) :=
    certificateRows.right.right.right.left
  have centralTX : SubgroupCentralizerCarrier mul a (mul t x) :=
    mulClosed centralT centralX
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) :=
    invClosed centralT
  exact mulClosed centralTX centralInvT
theorem SubgroupCentralizerCarrier_self_normalizes {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro centralT
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) := by
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralT
  have invInvSameT : hsame (inv (inv t)) t :=
    BEDC.Derived.GroupUp.group_left_inverse_involutive assocC leftId rightId mulCongr
      leftInv t
  have centralInvInvT : SubgroupCentralizerCarrier mul a (inv (inv t)) := by
    exact hsame_trans (mulCongr invInvSameT (hsame_refl a))
      (hsame_trans centralT (mulCongr (hsame_refl a) (hsame_symm invInvSameT)))
  constructor
  · intro x centralX
    have centralTX : SubgroupCentralizerCarrier mul a (mul t x) :=
      BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
        assocC rightId mulCongr centralT centralX
    exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralTX centralInvT
  · intro x centralX
    have centralInvTX : SubgroupCentralizerCarrier mul a (mul (inv t) x) :=
      BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
        assocC rightId mulCongr centralInvT centralX
    exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralInvTX centralInvInvT
protected theorem SubgroupCentralizerCarrier_self_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerNormalizer mul inv a t := by
  exact SubgroupCentralizerCarrier_self_normalizes
    assocC leftId rightId mulCongr leftInv rightInv
theorem SubgroupCentralizerNormalizer_kernel_classifier_refl
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerNormalizer mul inv a x -> SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerCarrier mul a (mul (inv x) x) := by
  intro normalizes
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    certificateRows.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv x) x) :=
    carrierTransport emptyCentral (hsame_symm (leftInv x))
  exact And.intro normalizes (And.intro normalizes kernelCentral)
protected theorem SubgroupCentralizerNormalizerQuotientClassifier_refl_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    {a x : BHist} :
    SubgroupCentralizerNormalizer mul inv a x -> SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a x ∧ Exists (fun z : BHist =>
            SubgroupCentralizerCarrier mul a z ∧ hsame x (mul x z)) := by
  intro normalizes
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    BEDC.Derived.GroupUp.group_centralizer_empty_unit_mem leftId rightId
  exact And.intro normalizes
    (And.intro normalizes
      (Exists.intro BHist.Empty (And.intro emptyCentral (hsame_symm (rightId x)))))
protected theorem SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t : BHist} :
    SubgroupCentralizerNormalizer mul inv a s -> SubgroupCentralizerNormalizer mul inv a t -> SubgroupCentralizerNormalizer mul inv a (mul s t) := by
  intro normalizesS normalizesT
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  constructor
  · intro x centralX
    have composed :=
      BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv
        (a := a) (s := s) (t := t) (x := x) normalizesS normalizesT centralX
    exact carrierTransport composed.left (hsame_symm composed.right.left)
  · intro x centralX
    have composed :=
      BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv
        (a := a) (s := s) (t := t) (x := x) normalizesS normalizesT centralX
    exact carrierTransport composed.right.right.left (hsame_symm composed.right.right.right)
protected theorem SubgroupCentralizerNormalizer_hsame_transport_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t : BHist} :
    SubgroupCentralizerNormalizer mul inv a s -> hsame s t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro normalizesS sameST
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    BEDC.Derived.GroupUp.group_inverse_congruence_from_laws
      assocC leftId rightId mulCongr leftInv rightInv
  constructor
  · intro x centralX
    have sameConjugate :
        hsame (mul (mul s x) (inv s)) (mul (mul t x) (inv t)) :=
      mulCongr (mulCongr sameST (hsame_refl x)) (invCongr sameST)
    exact carrierTransport (normalizesS.left x centralX) sameConjugate
  · intro x centralX
    have sameConjugate :
        hsame (mul (mul (inv s) x) (inv (inv s)))
          (mul (mul (inv t) x) (inv (inv t))) :=
      mulCongr (mulCongr (invCongr sameST) (hsame_refl x)) (invCongr (invCongr sameST))
    exact carrierTransport (normalizesS.right x centralX) sameConjugate
theorem SubgroupCentralizerQuotientKernel_hsame_transport
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x x' y y' : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y -> hsame x x' -> hsame y y' -> SubgroupCentralizerQuotientKernel mul inv a x' y' := by
  intro kernel sameXX' sameYY'
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    BEDC.Derived.GroupUp.group_inverse_congruence_from_laws
      assocC leftId rightId mulCongr leftInv rightInv
  have normalizesX' : SubgroupCentralizerNormalizer mul inv a x' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_hsame_transport_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel.left sameXX'
  have normalizesY' : SubgroupCentralizerNormalizer mul inv a y' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_hsame_transport_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel.right.left sameYY'
  have sameKernel :
      hsame (mul (inv x) y) (mul (inv x') y') :=
    mulCongr (invCongr sameXX') sameYY'
  have centralKernel : SubgroupCentralizerCarrier mul a (mul (inv x') y') :=
    carrierTransport kernel.right.right sameKernel
  exact And.intro normalizesX' (And.intro normalizesY' centralKernel)
theorem SubgroupCentralizerQuotientKernel_empty_fiber_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x <-> SubgroupCentralizerCarrier mul a x := by
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    certificateRows.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invEmpty : hsame (inv BHist.Empty) BHist.Empty :=
    BEDC.Derived.GroupUp.group_inverse_identity (mul := mul) (e := BHist.Empty)
      (inv := inv) rightId leftInv
  have displacementSameX : hsame (mul (inv BHist.Empty) x) x := by
    exact hsame_trans (mulCongr invEmpty (hsame_refl x)) (leftId x)
  constructor
  · intro classified
    exact carrierTransport classified.right.right displacementSameX
  · intro centralX
    have emptyNormalizer : SubgroupCentralizerNormalizer mul inv a BHist.Empty :=
      SubgroupCentralizerCarrier_self_normalizes
        assocC leftId rightId mulCongr leftInv rightInv emptyCentral
    have xNormalizer : SubgroupCentralizerNormalizer mul inv a x :=
      SubgroupCentralizerCarrier_self_normalizes
        assocC leftId rightId mulCongr leftInv rightInv centralX
    have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv BHist.Empty) x) :=
      carrierTransport centralX (hsame_symm displacementSameX)
    exact And.intro emptyNormalizer (And.intro xNormalizer kernelCentral)
theorem SubgroupCentralizerQuotientClassifier_kernel_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerQuotientClassifier mul inv a x y <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  constructor
  · intro classified
    cases classified.right.right with
    | intro c data =>
        have sameCDisplacement : hsame c (mul (inv x) y) := by
          have exposeUnit : hsame c (mul BHist.Empty c) :=
            hsame_symm (leftId c)
          have replaceUnit :
              hsame (mul BHist.Empty c) (mul (mul (inv x) x) c) :=
            mulCongr (hsame_symm (leftInv x)) (hsame_refl c)
          have reassoc :
              hsame (mul (mul (inv x) x) c) (mul (inv x) (mul x c)) :=
            assocC (inv x) x c
          have replaceTarget : hsame (mul (inv x) (mul x c)) (mul (inv x) y) :=
            mulCongr (hsame_refl (inv x)) data.right
          exact hsame_trans exposeUnit
            (hsame_trans replaceUnit (hsame_trans reassoc replaceTarget))
        exact And.intro classified.left
          (And.intro classified.right.left (carrierTransport data.left sameCDisplacement))
  · intro kernel
    have sameCoset : hsame (mul x (mul (inv x) y)) y := by
      have reassoc :
          hsame (mul x (mul (inv x) y)) (mul (mul x (inv x)) y) :=
        hsame_symm (assocC x (inv x) y)
      have collapseUnit : hsame (mul (mul x (inv x)) y) (mul BHist.Empty y) :=
        mulCongr (rightInv x) (hsame_refl y)
      exact hsame_trans reassoc (hsame_trans collapseUnit (leftId y))
    exact And.intro kernel.left
      (And.intro kernel.right.left
        (Exists.intro (mul (inv x) y) (And.intro kernel.right.right sameCoset)))
theorem SubgroupCentralizerQuotientKernel_witness_classifier_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    (SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ Exists (fun z : BHist =>
            SubgroupCentralizerCarrier mul a z ∧ hsame y (mul x z))) <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  constructor
  · intro witnessClassified
    cases witnessClassified.right.right with
    | intro z witness =>
        have sameZKernel : hsame z (mul (inv x) y) := by
          exact hsame_trans (hsame_symm (leftId z))
            (hsame_trans (hsame_symm (mulCongr (leftInv x) (hsame_refl z)))
              (hsame_trans (assocC (inv x) x z)
                (mulCongr (hsame_refl (inv x)) (hsame_symm witness.right))))
        have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv x) y) :=
          carrierTransport witness.left sameZKernel
        exact And.intro witnessClassified.left
          (And.intro witnessClassified.right.left kernelCentral)
  · intro kernelClassified
    have sameYWitness : hsame y (mul x (mul (inv x) y)) := by
      exact hsame_trans (hsame_symm (leftId y))
        (hsame_trans (hsame_symm (mulCongr (rightInv x) (hsame_refl y)))
          (assocC x (inv x) y))
    exact And.intro kernelClassified.left
      (And.intro kernelClassified.right.left
        (Exists.intro (mul (inv x) y)
          (And.intro kernelClassified.right.right sameYWitness)))
theorem SubgroupCentralizerNormalizerQuotientClassifier_kernel_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    (SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ Exists (fun z : BHist =>
            SubgroupCentralizerCarrier mul a z ∧ hsame y (mul x z))) <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  exact SubgroupCentralizerQuotientKernel_witness_classifier_iff
    assocC leftId rightId mulCongr leftInv rightInv
theorem SubgroupCentralizerNormalizerQuotientClassifier_kernel_iff_direct
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    (SubgroupCentralizerNormalizer mul inv a x ∧ SubgroupCentralizerNormalizer mul inv a y ∧ Exists (fun z : BHist =>
            SubgroupCentralizerCarrier mul a z ∧ hsame y (mul x z))) <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  constructor
  · intro classified
    cases classified.right.right with
    | intro z witness =>
        have invYToZ : hsame (mul (inv x) y) z := by
          exact hsame_trans (mulCongr (hsame_refl (inv x)) witness.right)
            (hsame_trans (hsame_symm (assocC (inv x) x z))
              (hsame_trans (mulCongr (leftInv x) (hsame_refl z)) (leftId z)))
        have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv x) y) :=
          carrierTransport witness.left (hsame_symm invYToZ)
        exact And.intro classified.left (And.intro classified.right.left kernelCentral)
  · intro kernel
    have xInvYToY : hsame (mul x (mul (inv x) y)) y := by
      exact hsame_trans (hsame_symm (assocC x (inv x) y))
        (hsame_trans (mulCongr (rightInv x) (hsame_refl y)) (leftId y))
    exact And.intro kernel.left
      (And.intro kernel.right.left
        (Exists.intro (mul (inv x) y)
          (And.intro kernel.right.right (hsame_symm xInvYToY))))
theorem SubgroupCentralizerRightCosetClassifier_quotientKernel_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerRightCosetClassifier mul inv a x y <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v := by
    intro u v centralU sameUV
    exact hsame_trans (mulCongr (hsame_symm sameUV) (hsame_refl a))
      (hsame_trans centralU (mulCongr (hsame_refl a) sameUV))
  constructor
  · intro classified
    cases classified.right.right with
    | intro z witness =>
        have sameKernel : hsame z (mul (inv x) y) := by
          exact Iff.mp
            (BEDC.Derived.GroupUp.group_left_mul_equation_exact_from_empty_unit
              assocC leftId mulCongr leftInv rightInv)
            (hsame_symm witness.right)
        exact And.intro classified.left
          (And.intro classified.right.left (carrierTransport witness.left sameKernel))
  · intro kernel
    let z := mul (inv x) y
    have sameCoset : hsame y (mul x z) := by
      exact hsame_symm
        (Iff.mpr
          (BEDC.Derived.GroupUp.group_left_mul_equation_exact_from_empty_unit
            assocC leftId mulCongr leftInv rightInv)
          (hsame_refl z))
    exact And.intro kernel.left
      (And.intro kernel.right.left (Exists.intro z (And.intro kernel.right.right sameCoset)))
protected theorem SubgroupCentralizerQuotientKernel_trans_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y z : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y -> SubgroupCentralizerQuotientKernel mul inv a y z -> SubgroupCentralizerQuotientKernel mul inv a x z := by
  intro leftKernel rightKernel
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> SubgroupCentralizerCarrier mul a v -> SubgroupCentralizerCarrier mul a (mul u v) :=
    certificateRows.right.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have productCentral :
      SubgroupCentralizerCarrier mul a
        (mul (mul (inv x) y) (mul (inv y) z)) :=
    mulClosed leftKernel.right.right rightKernel.right.right
  have cancelMiddle :
      hsame (mul (mul (inv x) y) (mul (inv y) z)) (mul (inv x) z) := by
    have reassocLeft :
        hsame (mul (mul (inv x) y) (mul (inv y) z))
          (mul (inv x) (mul y (mul (inv y) z))) :=
      assocC (inv x) y (mul (inv y) z)
    have reassocMiddle :
        hsame (mul y (mul (inv y) z)) (mul (mul y (inv y)) z) :=
      hsame_symm (assocC y (inv y) z)
    have cancelY :
        hsame (mul (mul y (inv y)) z) z :=
      hsame_trans (mulCongr (rightInv y) (hsame_refl z)) (leftId z)
    exact hsame_trans reassocLeft
      (hsame_trans (mulCongr (hsame_refl (inv x)) reassocMiddle)
        (mulCongr (hsame_refl (inv x)) cancelY))
  exact And.intro leftKernel.left
    (And.intro rightKernel.right.left (carrierTransport productCentral cancelMiddle))
theorem SubgroupCentralizerQuotientKernel_empty_right_fiber_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x BHist.Empty <-> SubgroupCentralizerCarrier mul a x := by
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have emptyCentral : SubgroupCentralizerCarrier mul a BHist.Empty :=
    certificateRows.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invClosed :
      forall {u : BHist}, SubgroupCentralizerCarrier mul a u -> SubgroupCentralizerCarrier mul a (inv u) :=
    certificateRows.right.right.right.left
  have displacementSameInvX : hsame (mul (inv x) BHist.Empty) (inv x) :=
    rightId (inv x)
  constructor
  · intro classified
    have centralInvX : SubgroupCentralizerCarrier mul a (inv x) :=
      carrierTransport classified.right.right displacementSameInvX
    have centralInvInvX : SubgroupCentralizerCarrier mul a (inv (inv x)) :=
      invClosed centralInvX
    have invInvSameX : hsame (inv (inv x)) x :=
      BEDC.Derived.GroupUp.group_left_inverse_involutive assocC leftId rightId mulCongr
        leftInv x
    exact carrierTransport centralInvInvX invInvSameX
  · intro centralX
    have xNormalizer : SubgroupCentralizerNormalizer mul inv a x :=
      SubgroupCentralizerCarrier_self_normalizes
        assocC leftId rightId mulCongr leftInv rightInv centralX
    have emptyNormalizer : SubgroupCentralizerNormalizer mul inv a BHist.Empty :=
      SubgroupCentralizerCarrier_self_normalizes
        assocC leftId rightId mulCongr leftInv rightInv emptyCentral
    have centralInvX : SubgroupCentralizerCarrier mul a (inv x) :=
      invClosed centralX
    have kernelCentral : SubgroupCentralizerCarrier mul a (mul (inv x) BHist.Empty) :=
      carrierTransport centralInvX (hsame_symm displacementSameInvX)
    exact And.intro xNormalizer (And.intro emptyNormalizer kernelCentral)
protected theorem SubgroupCentralizerQuotientKernel_symm_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y -> SubgroupCentralizerQuotientKernel mul inv a y x := by
  intro classified
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invClosed :
      forall {u : BHist}, SubgroupCentralizerCarrier mul a u -> SubgroupCentralizerCarrier mul a (inv u) :=
    certificateRows.right.right.right.left
  have inverseKernel : SubgroupCentralizerCarrier mul a (inv (mul (inv x) y)) :=
    invClosed classified.right.right
  have reverseKernel :
      hsame (inv (mul (inv x) y)) (mul (inv y) (inv (inv x))) :=
    BEDC.Derived.GroupUp.group_inverse_mul_reverse assocC leftId rightId mulCongr
      leftInv rightInv (inv x) y
  have invInvSameX : hsame (inv (inv x)) x :=
    BEDC.Derived.GroupUp.group_left_inverse_involutive assocC leftId rightId mulCongr
      leftInv x
  have displayedKernel :
      hsame (inv (mul (inv x) y)) (mul (inv y) x) :=
    hsame_trans reverseKernel (mulCongr (hsame_refl (inv y)) invInvSameX)
  exact And.intro classified.right.left
    (And.intro classified.left (carrierTransport inverseKernel displayedKernel))
theorem SubgroupCentralizerRightQuotientClassifier_kernel_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  have rows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v -> SubgroupCentralizerCarrier mul a v :=
    rows.right.right.right.right
  constructor
  · intro classified
    cases classified.right.right with
    | intro z witness =>
        have sameKernelZ : hsame (mul (inv x) y) z :=
          hsame_trans (mulCongr (hsame_refl (inv x)) witness.right)
            (hsame_trans (hsame_symm (assocC (inv x) x z))
              (hsame_trans (mulCongr (leftInv x) (hsame_refl z)) (leftId z)))
        exact And.intro classified.left
          (And.intro classified.right.left
            (carrierTransport witness.left (hsame_symm sameKernelZ)))
  · intro classified
    have sameRight : hsame (mul x (mul (inv x) y)) y :=
      hsame_trans (hsame_symm (assocC x (inv x) y))
        (hsame_trans (mulCongr (rightInv x) (hsame_refl y)) (leftId y))
    exact And.intro classified.left
      (And.intro classified.right.left
        (Exists.intro (mul (inv x) y)
          (And.intro classified.right.right (hsame_symm sameRight))))
theorem SubgroupCentralizerQuotientKernel_symm_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y -> SubgroupCentralizerQuotientKernel mul inv a y x := by
  exact BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_symm_from_empty_unit
    assocC leftId rightId mulCongr leftInv rightInv
theorem SubgroupCentralizerNormalizerQuotientClassifier_coincide
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (_rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerRightCosetClassifier mul inv a x y <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  exact SubgroupCentralizerRightCosetClassifier_quotientKernel_iff
    assocC leftId mulCongr leftInv rightInv
theorem SubgroupCentralizerQuotientKernel_classifier_laws
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z))) (leftId : forall x : BHist, hsame (mul BHist.Empty x) x) (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty) (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    (forall {x : BHist}, SubgroupCentralizerNormalizer mul inv a x -> SubgroupCentralizerQuotientKernel mul inv a x x) ∧ (forall {x y : BHist}, SubgroupCentralizerQuotientKernel mul inv a x y -> SubgroupCentralizerQuotientKernel mul inv a y x) ∧ (forall {x y z : BHist}, SubgroupCentralizerQuotientKernel mul inv a x y -> SubgroupCentralizerQuotientKernel mul inv a y z -> SubgroupCentralizerQuotientKernel mul inv a x z) := by
  constructor
  · intro x normalizes
    exact SubgroupCentralizerNormalizer_kernel_classifier_refl
      assocC leftId rightId mulCongr leftInv rightInv normalizes
  · constructor
    · intro x y kernel
      exact BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_symm_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv kernel
    · intro x y z kernelXY kernelYZ
      exact BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_trans_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv kernelXY kernelYZ
end BEDC.Derived.SubgroupUp

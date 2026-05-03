import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp
open BEDC.FKernel.NameCert

theorem QuotientGroupCentralizerNormalizer_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SubgroupCentralizerNormalizer mul inv a BHist.Empty := by
  intro x centralX
  have invEmpty : hsame (inv BHist.Empty) BHist.Empty := by
    exact hsame_trans (hsame_symm (leftId (inv BHist.Empty))) (rightInv BHist.Empty)
  have conjugateSame :
      hsame (mul (mul BHist.Empty x) (inv BHist.Empty)) x := by
    exact hsame_trans (mulCongr (leftId x) invEmpty) (rightId x)
  exact hsame_trans (mulCongr conjugateSame (hsame_refl a))
    (hsame_trans centralX (mulCongr (hsame_refl a) (hsame_symm conjugateSame)))

theorem QuotientGroupCentralizerNormalizer_empty_hsame_transport_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (invCongr : forall {x y : BHist}, hsame x y -> hsame (inv x) (inv y))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    hsame BHist.Empty t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro emptyT x centralX
  have conjugateToEmpty :
      hsame (mul (mul t x) (inv t))
        (mul (mul BHist.Empty x) (inv BHist.Empty)) := by
    exact mulCongr (mulCongr (hsame_symm emptyT) (hsame_refl x)) (invCongr (hsame_symm emptyT))
  have emptyConjugateCentral :
      SubgroupCentralizerCarrier mul a (mul (mul BHist.Empty x) (inv BHist.Empty)) := by
    exact QuotientGroupCentralizerNormalizer_empty_unit
      leftId rightId mulCongr rightInv x centralX
  exact hsame_trans (mulCongr conjugateToEmpty (hsame_refl a))
    (hsame_trans emptyConjugateCentral
      (mulCongr (hsame_refl a) (hsame_symm conjugateToEmpty)))

def QuotientGroupSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def QuotientGroupSingletonClassifier (h k : BHist) : Prop :=
  QuotientGroupSingletonCarrier h ∧ QuotientGroupSingletonCarrier k ∧ hsame h k

theorem QuotientGroupSingleton_semanticNameCert :
    SemanticNameCert QuotientGroupSingletonCarrier QuotientGroupSingletonCarrier
      QuotientGroupSingletonCarrier QuotientGroupSingletonClassifier := by
  have emptyCarrier : QuotientGroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

theorem QuotientGroupSingletonClassifier_visible_endpoint_absurd {p q k : BHist} :
    (QuotientGroupSingletonClassifier (BHist.e0 p) k -> False) ∧
      (QuotientGroupSingletonClassifier (BHist.e1 p) k -> False) ∧
        (QuotientGroupSingletonClassifier k (BHist.e0 q) -> False) ∧
          (QuotientGroupSingletonClassifier k (BHist.e1 q) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e0_empty classified.left
  · constructor
    · intro classified
      exact not_hsame_e1_empty classified.left
    · constructor
      · intro classified
        exact not_hsame_e0_empty classified.right.left
      · intro classified
        exact not_hsame_e1_empty classified.right.left

def CentralizerCosetCarrier (mul : BHist -> BHist -> BHist) (a repr h : BHist) : Prop :=
  SubgroupCentralizerCarrier mul a repr ∧ hsame h repr

def CentralizerCosetClassifier (mul : BHist -> BHist -> BHist) (a repr h k : BHist) : Prop :=
  CentralizerCosetCarrier mul a repr h ∧ CentralizerCosetCarrier mul a repr k ∧ hsame h k

theorem CentralizerCoset_semanticNameCert {mul : BHist -> BHist -> BHist} {a repr : BHist}
    (reprCentral : SubgroupCentralizerCarrier mul a repr) :
    SemanticNameCert (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetCarrier mul a repr) (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetClassifier mul a repr) := by
  constructor
  · constructor
    · exact Exists.intro repr (And.intro reprCentral (hsame_refl repr))
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
  · intro h carrier
    exact carrier
  · intro h carrier
    exact carrier

end BEDC.Derived.QuotientGroupUp

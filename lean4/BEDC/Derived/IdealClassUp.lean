import BEDC.Derived.CommRingUp
import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.IdealClassUp

open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.QuotientGroupUp

def IdealClassFractionalCarrier (h : BHist) : Prop :=
  CommRingSingletonCarrier h ∧ QuotientGroupSingletonCarrier h

def IdealClassPrincipalClassifier (h k : BHist) : Prop :=
  IdealClassFractionalCarrier h ∧ IdealClassFractionalCarrier k ∧ hsame h k

theorem IdealClassPrincipalClassifier_empty_boundary_laws :
    IdealClassPrincipalClassifier BHist.Empty BHist.Empty ∧
      (∀ {h k : BHist}, IdealClassPrincipalClassifier h k ->
        IdealClassPrincipalClassifier h BHist.Empty ∧
          IdealClassPrincipalClassifier k BHist.Empty) ∧
      (∀ {h k l : BHist}, IdealClassPrincipalClassifier h k ->
        IdealClassPrincipalClassifier k l -> IdealClassPrincipalClassifier h l) := by
  have emptyCarrier : IdealClassFractionalCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have emptyClassified : IdealClassPrincipalClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  exact And.intro emptyClassified
    (And.intro
      (by
        intro h k classified
        have leftBoundary : IdealClassPrincipalClassifier h BHist.Empty :=
          And.intro classified.left (And.intro emptyCarrier classified.left.left)
        have rightBoundary : IdealClassPrincipalClassifier k BHist.Empty :=
          And.intro classified.right.left
            (And.intro emptyCarrier classified.right.left.left)
        exact And.intro leftBoundary rightBoundary)
      (by
        intro h k l classifiedHK classifiedKL
        exact And.intro classifiedHK.left
          (And.intro classifiedKL.right.left
            (hsame_trans classifiedHK.right.right classifiedKL.right.right))))

theorem IdealClassFractionalCarrier_source_obligation {h k : BHist} :
    IdealClassFractionalCarrier h -> hsame h k ->
      IdealClassFractionalCarrier k ∧ CommRingSingletonClassifier k BHist.Empty ∧
        QuotientGroupSingletonClassifier k BHist.Empty := by
  intro carrierH sameHK
  have sameKEmpty : hsame k BHist.Empty :=
    hsame_trans (hsame_symm sameHK) carrierH.left
  have carrierK : IdealClassFractionalCarrier k :=
    And.intro sameKEmpty sameKEmpty
  have emptySame : hsame BHist.Empty BHist.Empty := hsame_refl BHist.Empty
  have commEmpty : CommRingSingletonCarrier BHist.Empty := emptySame
  have quotientEmpty : QuotientGroupSingletonCarrier BHist.Empty := emptySame
  have commRow : CommRingSingletonClassifier k BHist.Empty :=
    And.intro carrierK.left (And.intro commEmpty sameKEmpty)
  have quotientRow : QuotientGroupSingletonClassifier k BHist.Empty :=
    And.intro carrierK.right (And.intro quotientEmpty sameKEmpty)
  exact And.intro carrierK (And.intro commRow quotientRow)

end BEDC.Derived.IdealClassUp

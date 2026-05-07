import BEDC.Derived.CommRingUp
import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.IdealClassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.CommRingUp
open BEDC.Derived.QuotientGroupUp

def IdealClassFractionalCarrier (h : BHist) : Prop :=
  CommRingSingletonCarrier h ∧ QuotientGroupSingletonCarrier h

def IdealClassPrincipalClassifier (h k : BHist) : Prop :=
  IdealClassFractionalCarrier h ∧ IdealClassFractionalCarrier k ∧ hsame h k

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

theorem IdealClassPrincipalClassifier_semanticNameCert :
    SemanticNameCert IdealClassFractionalCarrier IdealClassFractionalCarrier
      IdealClassFractionalCarrier IdealClassPrincipalClassifier := by
  have emptyCarrier : IdealClassFractionalCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro _h _k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro _h _k _r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro _h _k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

theorem IdealClassQuotientOperation_empty_product_exactness {h k : BHist} :
    IdealClassFractionalCarrier h -> IdealClassFractionalCarrier k ->
      IdealClassPrincipalClassifier (CommRingSingletonMul h k) BHist.Empty ∧
        QuotientGroupSingletonClassifier (CommRingSingletonMul h k) BHist.Empty := by
  intro carrierH carrierK
  have productComm :
      CommRingSingletonClassifier (CommRingSingletonMul h k) BHist.Empty :=
    singleton_empty_history_commring_laws.right.right.right.left carrierH.left carrierK.left
  have productQuotient : QuotientGroupSingletonCarrier (CommRingSingletonMul h k) := by
    unfold CommRingSingletonMul
    exact hsame_refl BHist.Empty
  have emptyIdeal : IdealClassFractionalCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have productIdeal : IdealClassFractionalCarrier (CommRingSingletonMul h k) :=
    And.intro productComm.left productQuotient
  have principalRow :
      IdealClassPrincipalClassifier (CommRingSingletonMul h k) BHist.Empty :=
    And.intro productIdeal (And.intro emptyIdeal productQuotient)
  have quotientRow :
      QuotientGroupSingletonClassifier (CommRingSingletonMul h k) BHist.Empty :=
    And.intro productQuotient
      (And.intro (hsame_refl BHist.Empty) productQuotient)
  exact And.intro principalRow quotientRow

end BEDC.Derived.IdealClassUp

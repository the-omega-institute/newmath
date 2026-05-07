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

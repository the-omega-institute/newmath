import BEDC.Derived.CommRingUp
import BEDC.Derived.DedekindUp
import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.IdealClassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.CommRingUp
open BEDC.Derived.QuotientGroupUp

theorem IdealClassFractionalIdealCarrier_obligation :
    (exists h : BHist,
      CommRingSingletonCarrier h ∧ QuotientGroupSingletonCarrier h ∧
        CommRingSingletonClassifier h BHist.Empty ∧
          QuotientGroupSingletonClassifier h BHist.Empty) ∧
      SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
        CommRingSingletonCarrier CommRingSingletonClassifier ∧
        SemanticNameCert QuotientGroupSingletonCarrier QuotientGroupSingletonCarrier
          QuotientGroupSingletonCarrier QuotientGroupSingletonClassifier := by
  have commCert :
      SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
        CommRingSingletonCarrier CommRingSingletonClassifier :=
    singleton_empty_history_commring_laws.left
  have quotientCert :
      SemanticNameCert QuotientGroupSingletonCarrier QuotientGroupSingletonCarrier
        QuotientGroupSingletonCarrier QuotientGroupSingletonClassifier :=
    QuotientGroupSingleton_semanticNameCert
  have commEmpty : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have quotientEmpty : QuotientGroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have commClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
    commCert.core.equiv_refl commEmpty
  have quotientClassified : QuotientGroupSingletonClassifier BHist.Empty BHist.Empty :=
    quotientCert.core.equiv_refl quotientEmpty
  exact ⟨⟨BHist.Empty, commEmpty, quotientEmpty, commClassified, quotientClassified⟩,
    commCert, quotientCert⟩

theorem IdealClassQuotientOperation_exactness_obligation {h k : BHist} :
    CommRingSingletonCarrier h -> CommRingSingletonCarrier k ->
      QuotientGroupSingletonClassifier (CommRingSingletonMul h k) BHist.Empty ∧
        QuotientGroupSingletonClassifier (CommRingSingletonMul h BHist.Empty) h ∧
          QuotientGroupSingletonClassifier (CommRingSingletonMul BHist.Empty k) k := by
  intro carrierH carrierK
  have quotientCert :
      SemanticNameCert QuotientGroupSingletonCarrier QuotientGroupSingletonCarrier
        QuotientGroupSingletonCarrier QuotientGroupSingletonClassifier :=
    QuotientGroupSingleton_semanticNameCert
  have mulEmptyCarrier : QuotientGroupSingletonCarrier (CommRingSingletonMul h k) :=
    hsame_refl BHist.Empty
  have rightUnitCarrier : QuotientGroupSingletonCarrier (CommRingSingletonMul h BHist.Empty) :=
    hsame_refl BHist.Empty
  have leftUnitCarrier : QuotientGroupSingletonCarrier (CommRingSingletonMul BHist.Empty k) :=
    hsame_refl BHist.Empty
  have quotientH : QuotientGroupSingletonCarrier h := carrierH
  have quotientK : QuotientGroupSingletonCarrier k := carrierK
  exact ⟨quotientCert.core.equiv_refl mulEmptyCarrier,
    quotientCert.core.equiv_refl rightUnitCarrier |> fun rightEmpty =>
      ⟨⟨rightEmpty.left, quotientH, hsame_symm carrierH⟩,
        ⟨leftUnitCarrier, quotientK, hsame_symm carrierK⟩⟩⟩

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

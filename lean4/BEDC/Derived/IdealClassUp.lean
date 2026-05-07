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

end BEDC.Derived.IdealClassUp

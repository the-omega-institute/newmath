import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_vector_space_over_base :
    SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier ∧
      (forall {r m : BHist}, FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
          FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
            FieldSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m)) := by
  constructor
  · exact VecSpaceSingleton_semanticNameCert
  · intro r m _carrierR _carrierM
    have vecActionEmpty :
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    have fieldMulEmpty :
        FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    have actionMulCompatible :
        FieldSingletonClassifier (VecSpaceSingletonSmul r m) (FieldSingletonMul r m) :=
      And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    exact And.intro vecActionEmpty (And.intro fieldMulEmpty actionMulCompatible)

theorem FieldExtSingleton_certificate_obligation_package :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier ∧
      NameCert FieldSingletonCarrier FieldSingletonClassifier ∧
      NameCert VecSpaceSingletonCarrier VecSpaceSingletonClassifier ∧
      (forall {h : BHist}, FieldSingletonCarrier h -> Cont BHist.Empty h h) := by
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  have vecCert :
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier :=
    VecSpaceSingleton_semanticNameCert
  exact And.intro fieldCert
    (And.intro vecCert
      (And.intro fieldCert.core
        (And.intro vecCert.core
          (by
            intro h _carrierH
            exact cont_intro (append_empty_left h).symm))))

end BEDC.Derived.FieldExtUp

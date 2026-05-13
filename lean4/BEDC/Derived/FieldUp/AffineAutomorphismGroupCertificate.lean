import BEDC.Derived.FieldUp
import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.GroupUp

theorem FieldAffineAutomorphismGroupCertificate :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      GroupSingletonCarrier BHist.Empty ∧
      FieldSingletonClassifier
        (FieldSingletonAdd (FieldSingletonMul FieldSingletonOne BHist.Empty)
          FieldSingletonZero)
        BHist.Empty ∧
      FieldSingletonClassifier (FieldSingletonMul FieldSingletonOne FieldSingletonOne)
        FieldSingletonOne ∧
      (∀ (p : FieldSingletonNonZero FieldSingletonOne),
        FieldSingletonCarrier (FieldSingletonInv FieldSingletonOne p)) := by
  have fieldRows := singleton_empty_history_field_schema_laws
  have groupRows := GroupSingletonHistory_laws
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier := fieldRows.left
  have groupUnitCarrier : GroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyCarrier : FieldSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyClassified : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    fieldCert.core.equiv_refl emptyCarrier
  have addMulRow :
      FieldSingletonClassifier
        (FieldSingletonAdd (FieldSingletonMul FieldSingletonOne BHist.Empty)
          FieldSingletonZero)
        BHist.Empty := by
    exact emptyClassified
  have mulOneRow :
      FieldSingletonClassifier (FieldSingletonMul FieldSingletonOne FieldSingletonOne)
        FieldSingletonOne := by
    exact emptyClassified
  have inverseCarrier :
      ∀ (p : FieldSingletonNonZero FieldSingletonOne),
        FieldSingletonCarrier (FieldSingletonInv FieldSingletonOne p) := by
    intro p
    exact fieldRows.right.right.right.left p
  exact And.intro fieldCert
    (And.intro groupUnitCarrier
      (And.intro addMulRow
        (And.intro mulOneRow inverseCarrier)))

end BEDC.Derived.FieldUp

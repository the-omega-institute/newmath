import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp

theorem FieldExtSingletonInverse_row_vacuous_exactness {a : BHist}
    (p : FieldSingletonNonZero (FieldExtSingletonEmbedding a)) :
    FieldSingletonClassifier (FieldSingletonInv (FieldExtSingletonEmbedding a) p) BHist.Empty ∧
      Cont BHist.Empty (FieldSingletonInv (FieldExtSingletonEmbedding a) p)
        (FieldSingletonInv (FieldExtSingletonEmbedding a) p) := by
  exact False.elim (FieldSingletonNonZero_absurd p)

theorem FieldExtSingletonNonzeroDomain_absurd {a : BHist} :
    FieldSingletonCarrier a -> FieldSingletonNonZero a ->
      hsame BHist.Empty (BHist.e0 BHist.Empty) ∧ False := by
  intro _carrier nonzero
  have forced : hsame BHist.Empty (BHist.e0 BHist.Empty) :=
    FieldSingletonNonZero_empty_e0_forced nonzero
  exact And.intro forced (not_hsame_emp_e0 forced)

end BEDC.Derived.FieldExtUp

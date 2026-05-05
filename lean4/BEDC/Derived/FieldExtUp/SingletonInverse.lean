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

end BEDC.Derived.FieldExtUp

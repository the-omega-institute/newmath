import BEDC.Derived.AdeleUp
import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.ClassFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.AdeleUp
open BEDC.Derived.NumFieldUp

theorem ClassField_artin_frobenius_stability_obligations
    {base base' idele idele' extension extension' artin artin' frob frob' : BHist} :
    NumFieldRatReflexiveClassifier base base' ->
      AdeleHistoryCarrier idele ->
        AdeleHistoryCarrier idele' ->
          hsame idele idele' ->
            hsame extension extension' ->
              Cont base idele artin ->
                Cont base' idele' artin' ->
                  Cont artin extension frob ->
                    Cont artin' extension' frob' ->
                      hsame artin artin' ∧ hsame frob frob' := by
  intro baseClassified _ideleCarrier _ideleCarrier' sameIdele sameExtension artinRow
    artinRow' frobRow frobRow'
  have sameBase : hsame base base' :=
    baseClassified.right.right.right.right
  have sameArtin : hsame artin artin' :=
    cont_respects_hsame sameBase sameIdele artinRow artinRow'
  exact And.intro sameArtin
    (cont_respects_hsame sameArtin sameExtension frobRow frobRow')

end BEDC.Derived.ClassFieldUp

import BEDC.Derived.AdeleUp
import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ClassFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.AdeleUp
open BEDC.Derived.NumFieldUp
open BEDC.Derived.RatUp

theorem ClassFieldCarrierClassifier_obligation
    {base base' idele idele' carrier carrier' : BHist} :
    NumFieldReflexiveRationalCarrier base -> RatHistoryClassifier base base' ->
      AdeleHistoryCarrier idele -> hsame idele idele' -> Cont base idele carrier ->
        Cont base' idele' carrier' ->
          NumFieldReflexiveRationalCarrier base' ∧ AdeleHistoryCarrier idele' ∧
            hsame carrier carrier' := by
  intro baseCarrier baseClassified ideleCarrier sameIdele leftCont rightCont
  have numCert :
      SemanticNameCert NumFieldReflexiveRationalCarrier NumFieldReflexiveRationalCarrier
        NumFieldReflexiveRationalCarrier RatHistoryClassifier :=
    NumFieldReflexiveRational_semantic_name_certificate
  have adeleCert :
      SemanticNameCert AdeleHistoryCarrier AdeleHistoryCarrier AdeleHistoryCarrier hsame :=
    AdeleHistoryCarrier_semanticNameCert
  have baseCarrier' : NumFieldReflexiveRationalCarrier base' :=
    numCert.core.carrier_respects_equiv baseClassified baseCarrier
  have ideleCarrier' : AdeleHistoryCarrier idele' :=
    adeleCert.core.carrier_respects_equiv sameIdele ideleCarrier
  have sameCarrier : hsame carrier carrier' :=
    cont_respects_hsame baseClassified.right.right sameIdele leftCont rightCont
  exact And.intro baseCarrier' (And.intro ideleCarrier' sameCarrier)

theorem ClassFieldArtinFrobenius_stability_obligation
    {base base' idele idele' extension extension' artin artin' frob frob' : BHist} :
    NumFieldReflexiveRationalCarrier base -> RatHistoryClassifier base base' ->
      AdeleHistoryCarrier idele -> hsame idele idele' -> Cont base idele extension ->
        Cont base' idele' extension' -> Cont idele extension artin ->
          Cont idele' extension' artin' -> Cont extension base frob ->
            Cont extension' base' frob' ->
              hsame extension extension' ∧ hsame artin artin' ∧ hsame frob frob' := by
  intro _baseCarrier baseClassified _ideleCarrier sameIdele leftExtension rightExtension
    leftArtin rightArtin leftFrob rightFrob
  have sameExtension : hsame extension extension' :=
    cont_respects_hsame baseClassified.right.right sameIdele leftExtension rightExtension
  have sameArtin : hsame artin artin' :=
    cont_respects_hsame sameIdele sameExtension leftArtin rightArtin
  have sameFrob : hsame frob frob' :=
    cont_respects_hsame sameExtension baseClassified.right.right leftFrob rightFrob
  exact And.intro sameExtension (And.intro sameArtin sameFrob)

end BEDC.Derived.ClassFieldUp

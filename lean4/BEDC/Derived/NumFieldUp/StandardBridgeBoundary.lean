import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldUp_StdBridge :
    SemanticNameCert NumFieldRatReflexiveCarrier NumFieldRatReflexiveCarrier
        NumFieldRatReflexiveCarrier NumFieldRatReflexiveClassifier ∧
      (forall {h k : BHist}, NumFieldRatReflexiveClassifier h k ->
        RatHistoryClassifier h k) ∧
      (forall {h : BHist}, NumFieldRatReflexiveCarrier h ->
        RatHistoryCarrier h ∧ FieldExtRatReflexiveCarrier h ∧ Cont h BHist.Empty h) := by
  have scopedCert := NumFieldRatReflexive_scoped_namecert_certificate
  constructor
  · exact scopedCert.left
  · constructor
    · intro h k classified
      exact classified.right.right
    · intro h carrier
      exact And.intro carrier.left
        (And.intro
          (And.intro carrier.left
            (And.intro carrier.right.left carrier.right.right.right))
          (cont_right_unit h))

end BEDC.Derived.NumFieldUp

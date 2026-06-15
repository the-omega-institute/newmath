import BEDC.Derived.OptionUp.PayloadDescentExactness
import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageCarrier_certificate
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (payload_transport : forall a : BHist, S a -> T (delta.map a))
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) :
    (forall h : BHist, TaggedOptionHistoryCarrier S h ->
      exists k : BHist,
        TaggedOptionMapRel S T delta h k ∧
          TaggedOptionPayloadDescentImageCarrier S T delta k) ∧
      (forall k : BHist, TaggedOptionPayloadDescentImageCarrier S T delta k ->
        TaggedOptionHistoryCarrier T k) ∧
        (forall h h' k k' : BHist,
          TaggedOptionHistoryClassifier S RelS h h' ->
            TaggedOptionMapRel S T delta h k ->
              TaggedOptionMapRel S T delta h' k' ->
                TaggedOptionHistoryClassifier T RelT k k') := by
  -- BEDC touchpoint anchor: BHist NameCert hsame DescentCertificate
  constructor
  · intro h sourceCarrier
    have transported :=
      TaggedOptionMapRel_total_carrier_transport delta payload_transport sourceCarrier
    cases transported with
    | intro k data =>
        exact Exists.intro k
          (And.intro data.left (Exists.intro h (And.intro sourceCarrier data.left)))
  · constructor
    · intro k imageCarrier
      cases imageCarrier with
      | intro h imageData =>
          exact TaggedOptionMapRel_target_carrier delta imageData.right
    · intro h h' k k' sourceClass mapH mapH'
      exact TaggedOptionMapRel_preserves_classification delta cert source_hsame
        sourceClass mapH mapH'

end BEDC.Derived.OptionUp

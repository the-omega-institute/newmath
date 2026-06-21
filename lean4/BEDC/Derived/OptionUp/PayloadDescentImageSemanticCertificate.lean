import BEDC.Derived.OptionUp.PayloadDescentImageCertificate
import BEDC.Derived.OptionUp.PayloadDescentImageClassifierStability

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_semantic_certificate
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (payload_transport : forall a : BHist, S a -> T (delta.map a))
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) :
    SemanticNameCert (TaggedOptionPayloadDescentImageCarrier S T delta)
      (TaggedOptionHistoryCarrier T) (TaggedOptionHistoryCarrier T)
      (TaggedOptionPayloadDescentImageClassifier S T delta) := by
  -- BEDC touchpoint anchor: BHist NameCert SemanticNameCert DescentCertificate
  have imageCertificate :=
    TaggedOptionPayloadDescentImageCarrier_certificate delta payload_transport cert
      source_hsame
  have stability :=
    TaggedOptionPayloadDescentImageClassifier_stability_fields
      (S := S) (T := T) (RelS := RelS) (RelT := RelT) delta cert source_hsame
  exact {
    core := {
      carrier_inhabited := by
        cases NameCert.carrier_inhabited cert with
        | intro a sourceA =>
            have targetA : T (delta.map a) := payload_transport a sourceA
            exact Exists.intro (BHist.e1 (delta.map a))
              (Exists.intro (BHist.e1 a)
                (And.intro
                  (Or.inr
                    (Exists.intro a
                      (And.intro sourceA (hsame_refl (BHist.e1 a)))))
                  (Or.inr
                    (Exists.intro a
                      (And.intro sourceA
                        (And.intro targetA
                          (And.intro (hsame_refl (BHist.e1 a))
                            (hsame_refl (BHist.e1 (delta.map a))))))))))
      equiv_refl := by
        intro k image
        exact stability.left image
      equiv_symm := by
        intro k k' image
        exact stability.right.left image
      equiv_trans := by
        intro k l m left right
        exact
          TaggedOptionPayloadDescentImageClassifier_reflective_transitivity
            delta cert source_hsame reflects left right
      carrier_respects_equiv := by
        intro k k' image _source
        exact (stability.right.right image).right
    }
    pattern_sound := by
      intro k image
      exact imageCertificate.right.left k image
    ledger_sound := by
      intro k image
      exact imageCertificate.right.left k image
  }

end BEDC.Derived.OptionUp

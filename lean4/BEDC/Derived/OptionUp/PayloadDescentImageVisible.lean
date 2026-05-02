import BEDC.Derived.OptionUp.EndpointAbsurd
import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_visible_payload_exactness
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' u v : BHist} :
    (TaggedOptionPayloadDescentImageClassifier S T delta k k' ∧ T u ∧ T v ∧
        hsame k (BHist.e1 u) ∧ hsame k' (BHist.e1 v)) ↔
      T u ∧ T v ∧ hsame k (BHist.e1 u) ∧ hsame k' (BHist.e1 v) ∧
        ∃ a b : BHist,
          S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
            hsame u (delta.map a) ∧ hsame v (delta.map b) := by
  constructor
  · intro visible
    cases visible with
    | intro image rest =>
        cases rest with
        | intro targetU rest =>
            cases rest with
            | intro targetV rest =>
                cases rest with
                | intro sameK sameK' =>
                    exact
                      And.intro targetU
                        (And.intro targetV
                          (And.intro sameK
                            (And.intro sameK'
                              (TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
                                delta cert source_hsame image targetU targetV sameK sameK'))))
  · intro visible
    cases visible with
    | intro targetU rest =>
        cases rest with
        | intro targetV rest =>
            cases rest with
            | intro sameK rest =>
                cases rest with
                | intro sameK' payload =>
                    cases payload with
                    | intro a payload =>
                        cases payload with
                        | intro b data =>
                            have sameLeft : hsame k (BHist.e1 (delta.map a)) :=
                              hsame_trans sameK (hsame_e1_congr data.right.right.right.right.right.left)
                            have sameRight : hsame k' (BHist.e1 (delta.map b)) :=
                              hsame_trans sameK'
                                (hsame_e1_congr data.right.right.right.right.right.right)
                            have image :
                                TaggedOptionPayloadDescentImageClassifier S T delta k k' := by
                              apply
                                (TaggedOptionPayloadDescentImageClassifier_branch_exactness
                                  delta cert source_hsame).mpr
                              exact Or.inr
                                ⟨a, b, data.left, data.right.left, data.right.right.left,
                                  data.right.right.right.left,
                                  data.right.right.right.right.left, sameLeft, sameRight⟩
                            exact
                              And.intro image
                                (And.intro targetU
                                  (And.intro targetV (And.intro sameK sameK')))

theorem TaggedOptionPayloadDescentImageClassifier_visible_target_payload_classification
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (certS : NameCert S RelS)
    (certT : NameCert T RelT)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible T RelT) {k k' u v : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      T u →
        T v →
          hsame k (BHist.e1 u) →
            hsame k' (BHist.e1 v) →
              RelT u v := by
  intro image targetU targetV sameK sameK'
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_visible_payload_readback
      delta certS source_hsame image targetU targetV sameK sameK'
  cases readback with
  | intro a readback =>
      cases readback with
      | intro b data =>
          have relImage : RelT (delta.map a) (delta.map b) :=
            delta.respects data.right.right.left
          have relLeft : RelT u (delta.map a) :=
            target_hsame targetU data.right.right.right.left
              data.right.right.right.right.right.left
          have relRight : RelT (delta.map b) v :=
            target_hsame data.right.right.right.right.left targetV
              (hsame_symm data.right.right.right.right.right.right)
          exact NameCert.equiv_trans certT (NameCert.equiv_trans certT relLeft relImage) relRight

theorem TaggedOptionPayloadDescentImageClassifier_mixed_visible_tag_separation
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' u v : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' →
      (hsame k BHist.Empty → T v → hsame k' (BHist.e1 v) → False) ∧
        (T u → hsame k (BHist.e1 u) → hsame k' BHist.Empty → False) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  constructor
  · intro sameKEmpty _targetV sameK'Present
    cases branch with
    | inl absent =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameK'Present)
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro _b data =>
                exact not_hsame_emp_e1
                  (hsame_trans (hsame_symm sameKEmpty)
                    data.right.right.right.right.right.left)
  · intro _targetU sameKPresent sameK'Empty
    cases branch with
    | inl absent =>
        exact not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameKPresent)
    | inr present =>
        cases present with
        | intro _a present =>
            cases present with
            | intro b data =>
                exact not_hsame_emp_e1
                  (hsame_trans (hsame_symm sameK'Empty)
                    data.right.right.right.right.right.right)

theorem TaggedOptionPayloadDescentImageClassifier_public_constructor_normal_form
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
      TaggedOptionPayloadDescentImageCarrier S T delta k ∧
        TaggedOptionPayloadDescentImageCarrier S T delta k' ∧
          TaggedOptionHistoryClassifier T RelT k k' ∧
            (forall t : BHist,
              (hsame k (BHist.e0 t) -> False) ∧ (hsame k' (BHist.e0 t) -> False)) ∧
              (((hsame k BHist.Empty ∧ hsame k' BHist.Empty ∧
                    ((exists a : BHist, exists b : BHist,
                      S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧
                        T (delta.map b) ∧ hsame k (BHist.e1 (delta.map a)) ∧
                          hsame k' (BHist.e1 (delta.map b))) -> False))) ∨
                (exists a : BHist, exists b : BHist,
                  S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
                    hsame k (BHist.e1 (delta.map a)) ∧
                      hsame k' (BHist.e1 (delta.map b)) ∧
                        (hsame k BHist.Empty -> False) ∧
                          (hsame k' BHist.Empty -> False) ∧
                            (forall a' : BHist, forall b' : BHist,
                              S a' -> S b' -> RelS a' b' -> T (delta.map a') ->
                                T (delta.map b') -> hsame k (BHist.e1 (delta.map a')) ->
                                  hsame k' (BHist.e1 (delta.map b')) ->
                                    hsame (delta.map a) (delta.map a') ∧
                                      hsame (delta.map b) (delta.map b')))) := by
  intro image
  have certificate :=
    TaggedOptionPayloadDescentImageClassifier_certificate delta cert source_hsame image
  have zeroEndpoint :
      forall t : BHist,
        (hsame k (BHist.e0 t) -> False) ∧ (hsame k' (BHist.e0 t) -> False) := by
    intro t
    exact TaggedOptionHistoryClassifier_zero_endpoint_exclusion certificate.right.right
  have readback :=
    TaggedOptionPayloadDescentImageClassifier_pair_readback_single_valued
      delta cert source_hsame image
  exact And.intro certificate.left
    (And.intro certificate.right.left
      (And.intro certificate.right.right (And.intro zeroEndpoint readback)))

end BEDC.Derived.OptionUp

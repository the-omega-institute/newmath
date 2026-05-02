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

end BEDC.Derived.OptionUp

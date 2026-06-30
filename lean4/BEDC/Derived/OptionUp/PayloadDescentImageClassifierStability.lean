import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_stability_fields
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) :
    (forall {k : BHist},
      TaggedOptionPayloadDescentImageCarrier S T delta k ->
        TaggedOptionPayloadDescentImageClassifier S T delta k k) ∧
      (forall {k k' : BHist},
        TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
          TaggedOptionPayloadDescentImageClassifier S T delta k' k) ∧
        (forall {k k' : BHist},
          TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
            TaggedOptionPayloadDescentImageCarrier S T delta k ∧
              TaggedOptionPayloadDescentImageCarrier S T delta k') := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  constructor
  · intro k carrier
    exact
      (TaggedOptionPayloadDescentImageClassifier_self_exactness
        delta cert source_hsame).mpr carrier
  constructor
  · intro k k' image
    have branch :=
      (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
        image
    apply
      (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mpr
    cases branch with
    | inl absent =>
        exact Or.inl (And.intro absent.right absent.left)
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                exact Or.inr
                  (Exists.intro b
                    (Exists.intro a
                      (And.intro data.right.left
                        (And.intro data.left
                          (And.intro (NameCert.equiv_symm cert data.right.right.left)
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.left
                                (And.intro data.right.right.right.right.right.right
                                  data.right.right.right.right.right.left))))))))
  · intro k k' image
    have certified :=
      TaggedOptionPayloadDescentImageClassifier_certificate delta cert source_hsame image
    exact And.intro certified.left certified.right.left

end BEDC.Derived.OptionUp

import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem OptionHistoryClassifier_self_exactness {source : BHist -> Prop} {h : BHist} :
    OptionHistoryClassifier source h h ↔ OptionHistoryCarrier source h := by
  constructor
  · intro classifier
    exact classifier.left
  · intro carrier
    exact And.intro carrier (And.intro carrier (hsame_refl h))

theorem TaggedOptionHistoryClassifier_self_exactness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert S Rel) {h : BHist} :
    TaggedOptionHistoryClassifier S Rel h h <-> TaggedOptionHistoryCarrier S h := by
  constructor
  · intro classifier
    cases classifier with
    | inl absent =>
        exact Or.inl absent.left
    | inr present =>
        cases present with
        | intro a restA =>
            cases restA with
            | intro _b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro _sourceB rest =>
                        cases rest with
                        | intro sameH _rest =>
                            exact Or.inr (Exists.intro a (And.intro sourceA sameH))
  · intro carrier
    cases carrier with
    | inl absent =>
        exact Or.inl (And.intro absent absent)
    | inr present =>
        cases present with
        | intro a data =>
            cases data with
            | intro sourceA sameH =>
                exact Or.inr
                  (Exists.intro a
                    (Exists.intro a
                      (And.intro sourceA
                        (And.intro sourceA
                          (And.intro sameH
                            (And.intro sameH (NameCert.equiv_refl cert sourceA)))))))

end BEDC.Derived.OptionUp

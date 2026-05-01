import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistorySource_weakening {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (sourceWeakening : forall h : BHist, S h -> T h)
    (classifierWeakening :
      forall a b : BHist, S a -> S b -> RelS a b -> RelT a b) :
    (forall {h : BHist}, TaggedOptionHistoryCarrier S h -> TaggedOptionHistoryCarrier T h) /\
      (forall {h k : BHist},
        TaggedOptionHistoryClassifier S RelS h k ->
          TaggedOptionHistoryClassifier T RelT h k) := by
  constructor
  · intro h carrier
    cases carrier with
    | inl absent =>
        exact Or.inl absent
    | inr present =>
        cases present with
        | intro a data =>
            cases data with
            | intro sourceA samePresent =>
                exact Or.inr
                  (Exists.intro a (And.intro (sourceWeakening a sourceA) samePresent))
  · intro h k classifier
    cases classifier with
    | inl absentPair =>
        exact Or.inl absentPair
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK relAB =>
                                exact Or.inr
                                  (Exists.intro a
                                    (Exists.intro b
                                      (And.intro (sourceWeakening a sourceA)
                                        (And.intro (sourceWeakening b sourceB)
                                          (And.intro sameH
                                            (And.intro sameK
                                              (classifierWeakening a b sourceA sourceB
                                                relAB)))))))

theorem OptionHistorySource_monotonicity {S T : BHist → Prop}
    (source_mono : ∀ h : BHist, S h → T h) :
    (∀ {h : BHist}, OptionHistoryCarrier S h → OptionHistoryCarrier T h) ∧
      (∀ {h k : BHist}, OptionHistoryClassifier S h k →
        OptionHistoryClassifier T h k) := by
  have carrier_mono : ∀ {h : BHist},
      OptionHistoryCarrier S h → OptionHistoryCarrier T h := by
    intro h carrier
    cases carrier with
    | inl emptyCase =>
        exact Or.inl emptyCase
    | inr sourceCase =>
        exact Or.inr (source_mono h sourceCase)
  constructor
  · exact carrier_mono
  · intro h k classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            exact And.intro (carrier_mono carrierH)
              (And.intro (carrier_mono carrierK) sameHK)

end BEDC.Derived.OptionUp

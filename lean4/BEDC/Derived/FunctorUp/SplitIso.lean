import BEDC.Derived.FunctorUp.PrefixCarrier

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

theorem PrefixFunctorCarrier_split_iso_witness_pair_preserves
    {p a b f gLeft idA compA gRight idB compB : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b a gLeft ->
      CategoryHomCarrier a a idA -> Cont f gLeft compA -> CategoryHomCarrier a a compA ->
        hsame compA idA -> CategoryHomCarrier b a gRight -> CategoryHomCarrier b b idB ->
          Cont gRight f compB -> CategoryHomCarrier b b compB -> hsame compB idB ->
            ∃ prefLeftId prefLeftComp prefRightId prefRightComp : BHist,
              CategoryHomCarrier (append p a) (append p b) f ∧
                CategoryHomCarrier (append p b) (append p a) gLeft ∧
                  CategoryHomCarrier (append p a) (append p a) prefLeftId ∧
                    Cont f gLeft prefLeftComp ∧
                      CategoryHomCarrier (append p a) (append p a) prefLeftComp ∧
                        hsame prefLeftComp prefLeftId ∧
                          CategoryHomCarrier (append p b) (append p a) gRight ∧
                            CategoryHomCarrier (append p b) (append p b) prefRightId ∧
                              Cont gRight f prefRightComp ∧
                                CategoryHomCarrier (append p b) (append p b) prefRightComp ∧
                                  hsame prefRightComp prefRightId := by
  intro prefixCarrier left leftInverse leftIdentity leftComp leftComposite sameLeft
    rightInverse rightIdentity rightComp rightComposite sameRight
  exact
    Exists.intro idA
      (Exists.intro compA
        (Exists.intro idB
          (Exists.intro compB
            (And.intro (prefixCarrier.hom_preserves left)
              (And.intro (prefixCarrier.hom_preserves leftInverse)
                (And.intro (prefixCarrier.hom_preserves leftIdentity)
                  (And.intro leftComp
                    (And.intro (prefixCarrier.comp_preserves left leftInverse leftComp)
                      (And.intro sameLeft
                        (And.intro (prefixCarrier.hom_preserves rightInverse)
                          (And.intro (prefixCarrier.hom_preserves rightIdentity)
                            (And.intro rightComp
                              (And.intro
                                (prefixCarrier.comp_preserves rightInverse left rightComp)
                                sameRight)))))))))))))

theorem PrefixFunctorCarrier_split_iso_witness_pair_public_readback
    {p a b f gLeft idA compA gRight idB compB displayedLeft displayedRight : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b a gLeft ->
      CategoryHomCarrier a a idA -> Cont f gLeft compA -> CategoryHomCarrier a a compA ->
        hsame compA idA -> CategoryHomCarrier b a gRight -> CategoryHomCarrier b b idB ->
          Cont gRight f compB -> CategoryHomCarrier b b compB -> hsame compB idB ->
            CategoryHomCarrier (append p a) (append p a) displayedLeft ->
              CategoryHomCarrier (append p b) (append p b) displayedRight ->
                (∃ prefLeftId prefLeftComp prefRightId prefRightComp : BHist,
                  CategoryHomCarrier (append p a) (append p b) f ∧
                    CategoryHomCarrier (append p b) (append p a) gLeft ∧
                      CategoryHomCarrier (append p a) (append p a) prefLeftId ∧
                        Cont f gLeft prefLeftComp ∧
                          CategoryHomCarrier (append p a) (append p a) prefLeftComp ∧
                            hsame prefLeftComp prefLeftId ∧
                              CategoryHomCarrier (append p b) (append p a) gRight ∧
                                CategoryHomCarrier (append p b) (append p b) prefRightId ∧
                                  Cont gRight f prefRightComp ∧
                                    CategoryHomCarrier (append p b) (append p b)
                                      prefRightComp ∧
                                      hsame prefRightComp prefRightId) ∧
                  hsame compA displayedLeft ∧ hsame compB displayedRight := by
  intro prefixCarrier left leftInverse leftIdentity leftComp leftComposite sameLeft
    rightInverse rightIdentity rightComp rightComposite sameRight displayedLeftCarrier
    displayedRightCarrier
  have witnessPair :=
    PrefixFunctorCarrier_split_iso_witness_pair_preserves prefixCarrier left leftInverse
      leftIdentity leftComp leftComposite sameLeft rightInverse rightIdentity rightComp
      rightComposite sameRight
  have prefLeftComposite :
      CategoryHomCarrier (append p a) (append p a) compA :=
    prefixCarrier.comp_preserves left leftInverse leftComp
  have prefRightComposite :
      CategoryHomCarrier (append p b) (append p b) compB :=
    prefixCarrier.comp_preserves rightInverse left rightComp
  exact And.intro witnessPair
    (And.intro
      (CategoryHomCarrier_morphism_deterministic prefLeftComposite displayedLeftCarrier)
      (CategoryHomCarrier_morphism_deterministic prefRightComposite displayedRightCarrier))

end BEDC.Derived.FunctorUp

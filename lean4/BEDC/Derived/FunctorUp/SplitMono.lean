import BEDC.Derived.FunctorUp.PrefixCarrier

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

def CategorySplitMonomorphism (a b f : BHist) : Prop :=
  ∃ g : BHist, ∃ id : BHist, ∃ comp : BHist,
    CategoryHomCarrier a b f ∧
      CategoryHomCarrier b a g ∧
        CategoryHomCarrier a a id ∧
          Cont f g comp ∧ CategoryHomCarrier a a comp ∧ hsame comp id

def CategorySplitEpimorphism (a b f : BHist) : Prop :=
  ∃ g : BHist, ∃ id : BHist, ∃ comp : BHist,
    CategoryHomCarrier a b f ∧
      CategoryHomCarrier b a g ∧
        CategoryHomCarrier b b id ∧
          Cont g f comp ∧ CategoryHomCarrier b b comp ∧ hsame comp id

theorem PrefixFunctorCarrier_split_mono_witness_preserves {p a b f g id comp : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b a g ->
      CategoryHomCarrier a a id -> Cont f g comp -> CategoryHomCarrier a a comp ->
        hsame comp id ->
          ∃ prefId prefComp : BHist,
            CategoryHomCarrier (append p b) (append p a) g ∧
              CategoryHomCarrier (append p a) (append p a) prefId ∧
                Cont f g prefComp ∧
                  CategoryHomCarrier (append p a) (append p a) prefComp ∧
                    hsame prefComp prefId := by
  intro prefixCarrier left right identity compRel composite sameComposite
  exact
    Exists.intro id
      (Exists.intro comp
        (And.intro (prefixCarrier.hom_preserves right)
          (And.intro (prefixCarrier.hom_preserves identity)
              (And.intro compRel
                (And.intro (prefixCarrier.comp_preserves left right compRel) sameComposite)))))

theorem PrefixFunctorCarrier_split_monomorphism_preserves {p a b f : BHist} :
    PrefixFunctorCarrier p -> CategorySplitMonomorphism a b f ->
      CategorySplitMonomorphism (append p a) (append p b) f := by
  intro prefixCarrier splitMono
  cases splitMono with
  | intro g splitMono =>
      cases splitMono with
      | intro id splitMono =>
          cases splitMono with
          | intro comp splitData =>
              have preserved :=
                PrefixFunctorCarrier_split_mono_witness_preserves
                  prefixCarrier
                  splitData.left
                  splitData.right.left
                  splitData.right.right.left
                  splitData.right.right.right.left
                  splitData.right.right.right.right.left
                  splitData.right.right.right.right.right
              cases preserved with
              | intro prefId preserved =>
                  cases preserved with
                  | intro prefComp prefData =>
                      exact
                        Exists.intro g
                          (Exists.intro prefId
                            (Exists.intro prefComp
                              (And.intro (prefixCarrier.hom_preserves splitData.left)
                                prefData)))

theorem PrefixFunctorCarrier_split_epi_witness_preserves {p a b f g id comp : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> CategoryHomCarrier b a g ->
      CategoryHomCarrier b b id -> Cont g f comp -> CategoryHomCarrier b b comp ->
        hsame comp id ->
          ∃ prefId prefComp : BHist,
            CategoryHomCarrier (append p b) (append p a) g ∧
              CategoryHomCarrier (append p b) (append p b) prefId ∧
                Cont g f prefComp ∧
                  CategoryHomCarrier (append p b) (append p b) prefComp ∧
                    hsame prefComp prefId := by
  intro prefixCarrier left right identity compRel composite sameComposite
  exact
    Exists.intro id
      (Exists.intro comp
        (And.intro (prefixCarrier.hom_preserves right)
          (And.intro (prefixCarrier.hom_preserves identity)
            (And.intro compRel
              (And.intro (prefixCarrier.comp_preserves right left compRel) sameComposite)))))

theorem PrefixFunctorCarrier_split_epimorphism_preserves {p a b f : BHist} :
    PrefixFunctorCarrier p -> CategorySplitEpimorphism a b f ->
      CategorySplitEpimorphism (append p a) (append p b) f := by
  intro prefixCarrier splitEpi
  cases splitEpi with
  | intro g splitEpi =>
      cases splitEpi with
      | intro id splitEpi =>
          cases splitEpi with
          | intro comp splitData =>
              have preserved :=
                PrefixFunctorCarrier_split_epi_witness_preserves
                  prefixCarrier
                  splitData.left
                  splitData.right.left
                  splitData.right.right.left
                  splitData.right.right.right.left
                  splitData.right.right.right.right.left
                  splitData.right.right.right.right.right
              cases preserved with
              | intro prefId preserved =>
                  cases preserved with
                  | intro prefComp prefData =>
                      exact
                        Exists.intro g
                          (Exists.intro prefId
                            (Exists.intro prefComp
                              (And.intro (prefixCarrier.hom_preserves splitData.left)
                                prefData)))

end BEDC.Derived.FunctorUp

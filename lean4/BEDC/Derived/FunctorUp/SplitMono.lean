import BEDC.Derived.FunctorUp.PrefixCarrier

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

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

end BEDC.Derived.FunctorUp

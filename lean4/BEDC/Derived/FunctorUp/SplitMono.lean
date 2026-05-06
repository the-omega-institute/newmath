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

theorem CategorySplitMonomorphism_left_cancellative {a b x f u v fu fv : BHist} :
    CategorySplitMonomorphism a b f -> CategoryHomCarrier x a u ->
      CategoryHomCarrier x a v -> Cont u f fu -> Cont v f fv -> hsame fu fv ->
        hsame u v := by
  intro _splitMono _left _right leftComposite rightComposite sameComposite
  cases leftComposite
  cases rightComposite
  exact append_right_cancel (k := f) sameComposite

theorem CategorySplitMonomorphism_composition_closed {a b c f g u s t sf tg l lu : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier b a s ->
      Cont f s sf -> hsame sf BHist.Empty -> CategoryHomCarrier c b t -> Cont g t tg ->
        hsame tg BHist.Empty -> Cont f g u -> Cont t s l -> Cont u l lu ->
          CategorySplitMonomorphism a c u := by
  intro fCarrier gCarrier sCarrier sfRel sfEmpty tCarrier tgRel tgEmpty fgRel tsRel luRel
  have uCarrier : CategoryHomCarrier a c u :=
    CategoryHomCarrier_comp_closed fCarrier gCarrier fgRel
  have lCarrier : CategoryHomCarrier c a l :=
    CategoryHomCarrier_comp_closed tCarrier sCarrier tsRel
  have idCarrier : CategoryHomCarrier a a BHist.Empty :=
    CategoryHomCarrier_empty_identity fCarrier.left
  cases sfRel
  have fEmpty : f = BHist.Empty := (append_eq_empty_iff.mp sfEmpty).left
  have sEmpty : s = BHist.Empty := (append_eq_empty_iff.mp sfEmpty).right
  cases tgRel
  have gEmpty : g = BHist.Empty := (append_eq_empty_iff.mp tgEmpty).left
  have tEmpty : t = BHist.Empty := (append_eq_empty_iff.mp tgEmpty).right
  cases fEmpty
  cases sEmpty
  cases gEmpty
  cases tEmpty
  cases fgRel
  cases tsRel
  cases luRel
  exact
    Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (And.intro uCarrier
            (And.intro lCarrier
            (And.intro idCarrier
                (And.intro (cont_right_unit BHist.Empty)
                  (And.intro idCarrier rfl)))))))

end BEDC.Derived.FunctorUp

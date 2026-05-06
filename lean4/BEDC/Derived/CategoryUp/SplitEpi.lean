import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

theorem CategorySplitEpiWitness_right_cancellative {a b x f s sf u v fu fv : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a s -> Cont s f sf ->
      hsame sf BHist.Empty -> CategoryHomCarrier b x u -> CategoryHomCarrier b x v ->
        Cont f u fu -> Cont f v fv -> hsame fu fv -> hsame u v := by
  intro _ _ splitComposite splitEmpty _ _ leftComposite rightComposite sameComposite
  cases splitComposite
  have fEmpty : f = BHist.Empty := (append_eq_empty_iff.mp splitEmpty).right
  cases fEmpty
  cases leftComposite
  cases rightComposite
  exact (append_empty_left u).symm.trans (sameComposite.trans (append_empty_left v))

theorem CategorySplitEpiWitness_composition_closed {a b c f g u s t sf tg l lu : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier b a s ->
      Cont s f sf -> hsame sf BHist.Empty -> CategoryHomCarrier c b t -> Cont t g tg ->
        hsame tg BHist.Empty -> Cont f g u -> Cont t s l -> Cont l u lu ->
          CategoryHomCarrier a c u ∧ CategoryHomCarrier c a l ∧ hsame lu BHist.Empty := by
  intro fCarrier gCarrier sCarrier sfRel sfEmpty tCarrier tgRel tgEmpty fgRel tsRel luRel
  have uCarrier : CategoryHomCarrier a c u :=
    CategoryHomCarrier_comp_closed fCarrier gCarrier fgRel
  have lCarrier : CategoryHomCarrier c a l :=
    CategoryHomCarrier_comp_closed tCarrier sCarrier tsRel
  cases sfRel
  have sEmpty : s = BHist.Empty := (append_eq_empty_iff.mp sfEmpty).left
  have fEmpty : f = BHist.Empty := (append_eq_empty_iff.mp sfEmpty).right
  cases tgRel
  have tEmpty : t = BHist.Empty := (append_eq_empty_iff.mp tgEmpty).left
  have gEmpty : g = BHist.Empty := (append_eq_empty_iff.mp tgEmpty).right
  cases sEmpty
  cases fEmpty
  cases tEmpty
  cases gEmpty
  cases fgRel
  cases tsRel
  cases luRel
  exact And.intro uCarrier (And.intro lCarrier rfl)

end BEDC.Derived.CategoryUp

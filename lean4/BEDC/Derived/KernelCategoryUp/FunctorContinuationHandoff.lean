import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_functor_continuation_handoff
    {object hom identity composition associativity unit provenance name functorRead : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      UnaryHistory composition ->
        Cont hom composition functorRead ->
          UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
            UnaryHistory hom ∧ UnaryHistory functorRead ∧ Cont identity composition hom ∧
              Cont hom composition functorRead ∧ hsame associativity (append hom composition) ∧
                hsame unit identity ∧ hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont CategoryHomCarrier
  intro carrier compositionUnary homCompositionFunctor
  obtain ⟨objectUnary, identityCarrier, identityCompositionHom, associativitySame, unitSame,
    nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have homUnary : UnaryHistory hom :=
    unary_cont_closed identityUnary compositionUnary identityCompositionHom
  have functorUnary : UnaryHistory functorRead :=
    unary_cont_closed homUnary compositionUnary homCompositionFunctor
  exact
    ⟨objectUnary, identityCarrier, homUnary, functorUnary, identityCompositionHom,
      homCompositionFunctor, associativitySame, unitSame, nameSame⟩

end BEDC.Derived.KernelCategoryUp

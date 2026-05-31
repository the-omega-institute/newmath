import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_category_public_export_lock [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name categoryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      UnaryHistory composition ->
        Cont hom composition categoryRead ->
          PkgSig bundle categoryRead pkg ->
            UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
              Cont identity composition hom ∧ UnaryHistory categoryRead ∧
                Cont hom composition categoryRead ∧ hsame associativity (append hom composition) ∧
                  hsame unit identity ∧ hsame name (append provenance unit) ∧
                    PkgSig bundle categoryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame CategoryHomCarrier
  intro carrier compositionUnary homCompositionCategoryRead categoryPkg
  obtain ⟨objectUnary, identityCarrier, identityCompositionHom, associativitySame, unitSame,
    nameSame⟩ := carrier
  have identityUnary : UnaryHistory identity :=
    identityCarrier.right.right.left
  have homUnary : UnaryHistory hom :=
    unary_cont_closed identityUnary compositionUnary identityCompositionHom
  have categoryReadUnary : UnaryHistory categoryRead :=
    unary_cont_closed homUnary compositionUnary homCompositionCategoryRead
  exact
    ⟨objectUnary, identityCarrier, identityCompositionHom, categoryReadUnary,
      homCompositionCategoryRead, associativitySame, unitSame, nameSame, categoryPkg⟩

end BEDC.Derived.KernelCategoryUp

import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem KernelCategoryCertificateSurface
    {object hom identity composition associativity unit provenance name endpoint composite : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      Cont identity composition hom →
        Cont hom composite endpoint →
          UnaryHistory endpoint →
            hsame associativity (append hom composition) ∧ hsame unit identity ∧
              hsame name (append provenance unit) ∧ Cont identity composition hom ∧
                Cont hom composite endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier identityComposition homEndpoint _endpointUnary
  exact
    ⟨carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right, identityComposition, homEndpoint⟩

end BEDC.Derived.KernelCategoryUp

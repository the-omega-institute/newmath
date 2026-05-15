import BEDC.Derived.CategoryUp
import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem ContinuationMonadCarrier_category_hom_readback_correspondence
    {A B C f g u H K L N homRead : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      CategoryHomCarrier A C L ->
        Cont L N homRead ->
          UnaryHistory A ∧ UnaryHistory C ∧ UnaryHistory L ∧ UnaryHistory homRead ∧
            CategoryHomCarrier A C L ∧ Cont L N homRead ∧ hsame N L := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier UnaryHistory
  intro carrier homCarrier homReadCont
  obtain ⟨unaryA, _unaryF, _unaryG, _unaryU, _routeB, _routeC, _routeK, _routeL,
    sameEndpoint⟩ := carrier
  have unaryC : UnaryHistory C :=
    homCarrier.right.left
  have unaryL : UnaryHistory L :=
    homCarrier.right.right.left
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryHomRead : UnaryHistory homRead :=
    unary_cont_closed unaryL unaryN homReadCont
  exact ⟨unaryA, unaryC, unaryL, unaryHomRead, homCarrier, homReadCont, sameEndpoint⟩

end BEDC.Derived.ContinuationMonadUp

import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DerivedFunctorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DerivedFunctorCarrier
    (functor resolution homology degree resolved endpoint : BHist) : Prop :=
  UnaryHistory degree ∧ Cont functor resolution resolved ∧ Cont resolved homology endpoint

theorem DerivedFunctorCarrier_resolution_append_readback
    {functor resolution homology degree resolved endpoint : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      hsame resolved (append functor resolution) ∧
        hsame endpoint (append (append functor resolution) homology) ∧
          Cont functor resolution resolved ∧ Cont resolved homology endpoint := by
  intro carrier
  have resolvedReadback : hsame resolved (append functor resolution) :=
    carrier.right.left
  have endpointReadback :
      hsame endpoint (append (append functor resolution) homology) :=
    hsame_trans carrier.right.right
      (congrArg (fun h => append h homology) resolvedReadback)
  exact And.intro resolvedReadback
    (And.intro endpointReadback (And.intro carrier.right.left carrier.right.right))

end BEDC.Derived.DerivedFunctorUp

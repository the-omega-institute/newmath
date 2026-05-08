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

theorem DerivedFunctorCarrier_boundary_over_transported_resolution
    {functor resolution homology degree resolved endpoint resolution' resolved' endpoint' : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      hsame resolution resolution' ->
        Cont functor resolution' resolved' ->
          Cont resolved' homology endpoint' ->
            DerivedFunctorCarrier functor resolution' homology degree resolved' endpoint' ∧
              hsame resolved resolved' ∧ hsame endpoint endpoint' := by
  intro carrier sameResolution resolvedRow endpointRow
  have sameResolved : hsame resolved resolved' :=
    cont_respects_hsame (hsame_refl functor) sameResolution carrier.right.left resolvedRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameResolved (hsame_refl homology) carrier.right.right endpointRow
  exact And.intro
    (And.intro carrier.left (And.intro resolvedRow endpointRow))
    (And.intro sameResolved sameEndpoint)

end BEDC.Derived.DerivedFunctorUp

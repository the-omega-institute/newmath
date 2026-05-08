import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SimplicialSetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SimplicialSetSimplexRowCarrier
    (functor finite endpoint package route : BHist) : Prop :=
  UnaryHistory functor ∧ UnaryHistory finite ∧ UnaryHistory package ∧
    Cont functor finite endpoint ∧ Cont endpoint package route

def SimplicialSetFaceDegeneracyClassifier
    (functor finite endpoint package route functor' finite' endpoint' package' route' : BHist) :
    Prop :=
  hsame functor functor' ∧ hsame finite finite' ∧ hsame endpoint endpoint' ∧
    hsame package package' ∧ hsame route route'

theorem SimplicialSetFaceDegeneracyClassifier_ledger_stability
    {functor functor' finite finite' endpoint endpoint' package package' route route' :
      BHist} :
    SimplicialSetSimplexRowCarrier functor finite endpoint package route ->
      SimplicialSetSimplexRowCarrier functor' finite' endpoint' package' route' ->
        hsame functor functor' ->
          hsame finite finite' ->
            hsame package package' ->
              SimplicialSetFaceDegeneracyClassifier functor finite endpoint package route
                  functor' finite' endpoint' package' route' ∧
                hsame endpoint endpoint' ∧ hsame route route' := by
  intro carrier carrier' sameFunctor sameFinite samePackage
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameFunctor sameFinite carrier.right.right.right.left
      carrier'.right.right.right.left
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEndpoint samePackage carrier.right.right.right.right
      carrier'.right.right.right.right
  exact And.intro
    (And.intro sameFunctor
      (And.intro sameFinite
        (And.intro sameEndpoint (And.intro samePackage sameRoute))))
    (And.intro sameEndpoint sameRoute)

end BEDC.Derived.SimplicialSetUp

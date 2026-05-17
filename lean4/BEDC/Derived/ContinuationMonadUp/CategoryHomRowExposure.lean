import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_category_hom_row_exposure [AskSetup] [PackageSetup]
    {A B C f g u H K L N category : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N category →
        PkgSig bundle category pkg →
          UnaryHistory L ∧ UnaryHistory N ∧ UnaryHistory category ∧
            Cont L N category ∧ hsame N L ∧ PkgSig bundle category pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg
  intro carrier categoryRoute categoryPkg
  obtain ⟨_unaryA, unaryF, unaryG, unaryU, _routeB, _routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryCategory : UnaryHistory category :=
    unary_cont_closed unaryL unaryN categoryRoute
  exact
    ⟨unaryL, unaryN, unaryCategory, categoryRoute, sameEndpoint, categoryPkg⟩

end BEDC.Derived.ContinuationMonadUp

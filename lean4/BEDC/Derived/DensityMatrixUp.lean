import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.DensityMatrixUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive DensityMatrixAffineMixtureSpine (density : BHist -> Prop) : BHist -> Prop where
  | atom {rho : BHist} :
      density rho -> UnaryHistory rho -> DensityMatrixAffineMixtureSpine density rho
  | mix {rho sigma out : BHist} :
      DensityMatrixAffineMixtureSpine density rho ->
        DensityMatrixAffineMixtureSpine density sigma ->
          Cont rho sigma out -> DensityMatrixAffineMixtureSpine density out

theorem DensityMatrixAffineMixtureSpine_finite_closure
    {density : BHist -> Prop} {rho : BHist}
    (binaryClosed :
      forall {left right out : BHist},
        density left -> density right -> Cont left right out -> density out) :
    DensityMatrixAffineMixtureSpine density rho -> density rho := by
  intro spine
  induction spine with
  | atom densityRho _ =>
      exact densityRho
  | mix leftSpine rightSpine route leftDensity rightDensity =>
      exact binaryClosed leftDensity rightDensity route

theorem DensityMatrixAffineMixtureSpine_binary_convex_closure
    {density : BHist -> Prop} {rho sigma out : BHist}
    (rhoDensity : density rho) (rhoUnary : UnaryHistory rho)
    (sigmaDensity : density sigma) (sigmaUnary : UnaryHistory sigma)
    (route : Cont rho sigma out)
    (binaryClosed :
      forall {left right result : BHist},
        density left -> density right -> Cont left right result -> density result) :
    density out ∧ DensityMatrixAffineMixtureSpine density out := by
  have outDensity : density out :=
    binaryClosed rhoDensity sigmaDensity route
  have rhoSpine : DensityMatrixAffineMixtureSpine density rho :=
    DensityMatrixAffineMixtureSpine.atom rhoDensity rhoUnary
  have sigmaSpine : DensityMatrixAffineMixtureSpine density sigma :=
    DensityMatrixAffineMixtureSpine.atom sigmaDensity sigmaUnary
  exact And.intro outDensity
    (DensityMatrixAffineMixtureSpine.mix rhoSpine sigmaSpine route)

theorem DensityMatrixAffineMixtureSpine_unary_endpoint
    {density : BHist -> Prop} {rho : BHist} :
    DensityMatrixAffineMixtureSpine density rho -> UnaryHistory rho := by
  intro spine
  induction spine with
  | atom _ rhoUnary =>
      exact rhoUnary
  | mix _ _ route leftUnary rightUnary =>
      exact unary_cont_closed leftUnary rightUnary route

end BEDC.Derived.DensityMatrixUp

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

end BEDC.Derived.DensityMatrixUp

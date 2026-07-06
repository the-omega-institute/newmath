import BEDC.Derived.FaberSchauderSystemUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FaberSchauderSystemUp

open BEDC.Derived
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FaberSchauderSystemCarrier [AskSetup] [PackageSetup]
    (D H S C U R T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory S ∧ UnaryHistory C ∧
    UnaryHistory U ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FaberSchauderSystemCarrier_dyadic_hat_support [AskSetup] [PackageSetup]
    {D H S C U R T P N hatRead supportRead coeffRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FaberSchauderSystemCarrier D H S C U R T P N bundle pkg ->
      Cont D H hatRead ->
        Cont hatRead S supportRead ->
          Cont supportRead C coeffRead ->
            Cont coeffRead U budgetRead ->
              UnaryHistory hatRead ∧ UnaryHistory supportRead ∧ UnaryHistory coeffRead ∧
                UnaryHistory budgetRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier dyadicHatRoute hatSupportRoute supportCoeffRoute coeffBudgetRoute
  obtain ⟨dUnary, hUnary, sUnary, cUnary, uUnary, _rUnary, _tUnary, _pUnary, _nUnary,
    pPkg, nPkg⟩ := carrier
  have hatUnary : UnaryHistory hatRead :=
    unary_cont_closed dUnary hUnary dyadicHatRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed hatUnary sUnary hatSupportRoute
  have coeffUnary : UnaryHistory coeffRead :=
    unary_cont_closed supportUnary cUnary supportCoeffRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed coeffUnary uUnary coeffBudgetRoute
  exact ⟨hatUnary, supportUnary, coeffUnary, budgetUnary, pPkg, nPkg⟩

end BEDC.Derived.FaberSchauderSystemUp

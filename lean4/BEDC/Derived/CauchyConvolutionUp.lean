import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyConvolutionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyConvolutionCarrier [AskSetup] [PackageSetup]
    (F G K A D R E H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory A ∧
    UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont F G K ∧ Cont K A D ∧ Cont D R E ∧ Cont E N endpoint ∧
          PkgSig bundle endpoint pkg

theorem CauchyConvolutionTailBudgetCompatibility [AskSetup] [PackageSetup]
    {F G K A D R E H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvolutionCarrier F G K A D R E H C P N endpoint bundle pkg ->
      UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory A ∧
        UnaryHistory D ∧ UnaryHistory R ∧ Cont F G K ∧ Cont K A D ∧
          Cont D R E ∧ Cont E N endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨fUnary, gUnary, kUnary, aUnary, dUnary, rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _endpointUnary, sourceConvolution, convolutionBudget,
    budgetHandoff, sealEndpoint, pkgSig⟩ := carrier
  exact
    ⟨fUnary, gUnary, kUnary, aUnary, dUnary, rUnary, sourceConvolution,
      convolutionBudget, budgetHandoff, sealEndpoint, pkgSig⟩

end BEDC.Derived.CauchyConvolutionUp

import BEDC.Derived.StepIndexedTotalHostUp

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StepIndexedTotalHostCarrier_sibling_boundary [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert sibling :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      UnaryHistory sibling →
        Cont trace bounded sibling →
          UnaryHistory trace ∧ UnaryHistory bounded ∧ UnaryHistory sibling ∧
            Cont trace bounded sibling ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier BHist ProbeBundle Pkg Cont PkgSig
  intro carrier siblingUnary siblingRoute
  exact
    ⟨carrier.trace_unary, carrier.bounded_unary, siblingUnary, siblingRoute,
      carrier.provenance_pkg⟩

end BEDC.Derived.StepIndexedTotalHostUp

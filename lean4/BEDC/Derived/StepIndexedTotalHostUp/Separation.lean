import BEDC.Derived.StepIndexedTotalHostUp

namespace BEDC.Derived.StepIndexedTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StepIndexedTotalHostCarrier_separation [AskSetup] [PackageSetup]
    {host fuel trace normal bounded refusal transport route provenance nameCert
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StepIndexedTotalHostCarrier host fuel trace normal bounded refusal transport route
        provenance nameCert bundle pkg →
      Cont normal refusal boundaryRead →
        PkgSig bundle boundaryRead pkg →
          UnaryHistory host ∧ UnaryHistory fuel ∧ UnaryHistory trace ∧
            UnaryHistory normal ∧ UnaryHistory bounded ∧ UnaryHistory refusal ∧
              UnaryHistory boundaryRead ∧ Cont host fuel trace ∧
                Cont trace bounded normal ∧ Cont normal refusal boundaryRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: StepIndexedTotalHostCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier boundaryRoute boundaryPkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed carrier.normal_unary carrier.refusal_unary boundaryRoute
  exact
    ⟨carrier.host_unary, carrier.fuel_unary, carrier.trace_unary,
      carrier.normal_unary, carrier.bounded_unary, carrier.refusal_unary,
      boundaryUnary, carrier.host_fuel_trace, carrier.trace_bounded_normal,
      boundaryRoute, carrier.provenance_pkg, boundaryPkg⟩

end BEDC.Derived.StepIndexedTotalHostUp

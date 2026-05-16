import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_admission_obligation [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
        UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory selector ∧
          UnaryHistory disclosure ∧ UnaryHistory transport ∧ UnaryHistory route ∧
            UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont request windows dyadic ∧
              Cont dyadic handoff realSeal ∧ Cont selector disclosure transport ∧
                Cont transport route nameRow ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.selector_unary,
      carrier.disclosure_unary, carrier.transport_unary, carrier.route_unary,
      carrier.provenance_unary, carrier.nameRow_unary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal, carrier.selector_disclosure_transport,
      carrier.transport_route_nameRow, carrier.provenance_pkg, carrier.nameRow_pkg⟩

end BEDC.Derived.RealWindowBudgetUp

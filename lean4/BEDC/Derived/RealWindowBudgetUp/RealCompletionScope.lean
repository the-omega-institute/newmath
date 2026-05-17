import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_real_completion_scope [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont handoff realSeal endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory selector ∧
              UnaryHistory disclosure ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory endpoint ∧
                  Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                    Cont handoff realSeal endpoint ∧ Cont selector disclosure transport ∧
                      Cont transport route nameRow ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle nameRow pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier handoffRealSealEndpoint endpointPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffRealSealEndpoint
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.selector_unary,
      carrier.disclosure_unary, carrier.transport_unary, carrier.route_unary,
      carrier.provenance_unary, carrier.nameRow_unary, endpointUnary,
      carrier.request_windows_dyadic, carrier.dyadic_handoff_realSeal, handoffRealSealEndpoint,
      carrier.selector_disclosure_transport, carrier.transport_route_nameRow,
      carrier.provenance_pkg, carrier.nameRow_pkg, endpointPkg⟩

end BEDC.Derived.RealWindowBudgetUp

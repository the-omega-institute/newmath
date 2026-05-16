import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure RealWindowBudgetCarrier [AskSetup] [PackageSetup]
    (request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop where
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  request_unary : UnaryHistory request
  windows_unary : UnaryHistory windows
  dyadic_unary : UnaryHistory dyadic
  handoff_unary : UnaryHistory handoff
  realSeal_unary : UnaryHistory realSeal
  selector_unary : UnaryHistory selector
  disclosure_unary : UnaryHistory disclosure
  transport_unary : UnaryHistory transport
  route_unary : UnaryHistory route
  provenance_unary : UnaryHistory provenance
  nameRow_unary : UnaryHistory nameRow
  request_windows_dyadic : Cont request windows dyadic
  dyadic_handoff_realSeal : Cont dyadic handoff realSeal
  selector_disclosure_transport : Cont selector disclosure transport
  transport_route_nameRow : Cont transport route nameRow
  provenance_pkg : PkgSig bundle provenance pkg
  nameRow_pkg : PkgSig bundle nameRow pkg

theorem RealWindowBudgetCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg →
      Cont handoff realSeal endpoint →
        PkgSig bundle endpoint pkg →
          UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory endpoint ∧
              Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                Cont handoff realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier handoff_realSeal_endpoint endpoint_pkg
  constructor
  · exact carrier.request_unary
  · constructor
    · exact carrier.windows_unary
    · constructor
      · exact carrier.dyadic_unary
      · constructor
        · exact carrier.handoff_unary
        · constructor
          · exact carrier.realSeal_unary
          · constructor
            · exact unary_cont_closed carrier.handoff_unary carrier.realSeal_unary
                handoff_realSeal_endpoint
            · constructor
              · exact carrier.request_windows_dyadic
              · constructor
                · exact carrier.dyadic_handoff_realSeal
                · constructor
                  · exact handoff_realSeal_endpoint
                  · constructor
                    · exact carrier.provenance_pkg
                    · exact endpoint_pkg

end BEDC.Derived.RealWindowBudgetUp

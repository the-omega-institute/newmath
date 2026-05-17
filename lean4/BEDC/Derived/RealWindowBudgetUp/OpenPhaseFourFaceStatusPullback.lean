import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_open_phase_four_face_status_pullback
    [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance nameRow
      selectorRead visibleRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg ->
      Cont request selector selectorRead ->
        Cont selectorRead disclosure visibleRead ->
          Cont handoff realSeal endpoint ->
            PkgSig bundle visibleRead pkg ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
                  UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory selector ∧
                    UnaryHistory disclosure ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                      UnaryHistory provenance ∧ UnaryHistory nameRow ∧
                        UnaryHistory selectorRead ∧ UnaryHistory visibleRead ∧
                          UnaryHistory endpoint ∧ Cont request windows dyadic ∧
                            Cont dyadic handoff realSeal ∧ Cont selector disclosure transport ∧
                              Cont transport route nameRow ∧
                                Cont request selector selectorRead ∧
                                  Cont selectorRead disclosure visibleRead ∧
                                    Cont handoff realSeal endpoint ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle nameRow pkg ∧
                                          PkgSig bundle visibleRead pkg ∧
                                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorReadRoute visibleReadRoute endpointRoute visiblePkg endpointPkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed carrier.request_unary carrier.selector_unary selectorReadRoute
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed selectorReadUnary carrier.disclosure_unary visibleReadRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary endpointRoute
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.selector_unary,
      carrier.disclosure_unary, carrier.transport_unary, carrier.route_unary,
      carrier.provenance_unary, carrier.nameRow_unary, selectorReadUnary,
      visibleReadUnary, endpointUnary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal, carrier.selector_disclosure_transport,
      carrier.transport_route_nameRow, selectorReadRoute, visibleReadRoute,
      endpointRoute, carrier.provenance_pkg, carrier.nameRow_pkg, visiblePkg,
      endpointPkg⟩

end BEDC.Derived.RealWindowBudgetUp

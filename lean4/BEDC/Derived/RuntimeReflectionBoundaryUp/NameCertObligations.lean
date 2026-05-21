import BEDC.Derived.RuntimeReflectionBoundaryUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.RuntimeReflectionBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RuntimeReflectionBoundary_runtime_request_refusal_route_unary_closure
    {selfDescription runtimeRequest executionRefusal boundaryReport requestRead refusalRead
      reportRead : BHist} :
    UnaryHistory selfDescription ->
      UnaryHistory runtimeRequest ->
        UnaryHistory executionRefusal ->
          UnaryHistory boundaryReport ->
            Cont selfDescription runtimeRequest requestRead ->
              Cont requestRead executionRefusal refusalRead ->
                Cont refusalRead boundaryReport reportRead ->
                  UnaryHistory requestRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory reportRead ∧
                      Cont selfDescription runtimeRequest requestRead ∧
                        Cont requestRead executionRefusal refusalRead ∧
                          Cont refusalRead boundaryReport reportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro selfDescriptionUnary runtimeRequestUnary executionRefusalUnary boundaryReportUnary
    requestCont refusalCont reportCont
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed selfDescriptionUnary runtimeRequestUnary requestCont
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed requestReadUnary executionRefusalUnary refusalCont
  have reportReadUnary : UnaryHistory reportRead :=
    unary_cont_closed refusalReadUnary boundaryReportUnary reportCont
  exact
    ⟨requestReadUnary, refusalReadUnary, reportReadUnary, requestCont, refusalCont, reportCont⟩

end BEDC.Derived.RuntimeReflectionBoundaryUp

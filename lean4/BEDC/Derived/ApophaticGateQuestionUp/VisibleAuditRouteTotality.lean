import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_visible_audit_route_totality
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead consumerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        Cont auditRead nameRow consumerRead →
          PkgSig bundle consumerRead pkg →
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
              UnaryHistory readback ∧ UnaryHistory auditRead ∧ UnaryHistory consumerRead ∧
                Cont socket question readback ∧ Cont question refusal route ∧
                  Cont readback route auditRead ∧ Cont auditRead nameRow consumerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier auditReadRoute consumerReadRoute consumerReadPkg
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditReadRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed auditReadUnary nameRowUnary consumerReadRoute
  exact
    ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, auditReadUnary,
      consumerReadUnary, socketQuestionReadback, questionRefusalRoute, auditReadRoute,
      consumerReadRoute, provenancePkg, consumerReadPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp

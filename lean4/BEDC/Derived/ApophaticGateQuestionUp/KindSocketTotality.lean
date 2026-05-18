import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_kind_socket_totality [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead
      transportedRefusal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        hsame refusal transportedRefusal →
          UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
            UnaryHistory auditRead ∧ Cont socket question readback ∧
              Cont question refusal route ∧ hsame readback (append socket question) ∧
                hsame transportedRefusal refusal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier readbackRouteAudit refusalTransport
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  exact
    ⟨socketUnary, questionUnary, refusalUnary, auditUnary, socketQuestionReadback,
      questionRefusalRoute, readbackSameSourceQuestion, hsame_symm refusalTransport,
      provenancePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp

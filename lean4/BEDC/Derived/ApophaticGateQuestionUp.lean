import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApophaticGateQuestionCarrier [AskSetup] [PackageSetup]
    (socket question refusal readback transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
    UnaryHistory readback ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont socket question readback ∧
        Cont question refusal route ∧ Cont refusal readback transport ∧
          Cont readback route nameRow ∧ hsame readback (append socket question) ∧
            PkgSig bundle provenance pkg

theorem ApophaticGateQuestionCarrier_source_before_question_route
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory readback ∧
          Cont socket question readback ∧ hsame readback (append socket question) ∧
            UnaryHistory auditRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier auditRoute
  obtain ⟨socketUnary, questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  exact
    ⟨socketUnary, questionUnary, readbackUnary, socketQuestionReadback,
      readbackSameSourceQuestion, auditUnary, provenancePkg⟩

theorem ApophaticGateQuestionCarrier_refusal_audit_ledger
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
          UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont question refusal route ∧
            Cont refusal readback transport ∧ Cont readback route nameRow ∧
              UnaryHistory auditRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier auditRoute
  obtain ⟨_socketUnary, _questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketQuestionReadback,
    questionRefusalRoute, refusalReadbackTransport, readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  exact
    ⟨refusalUnary, transportUnary, routeUnary, provenanceUnary, nameRowUnary,
      questionRefusalRoute, refusalReadbackTransport, readbackRouteNameRow, auditUnary,
      provenancePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
